const http = require("http");
const https = require("https");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");

const PORT = process.env.PORT || 4000;
const OTP_TTL_MS = 3 * 60 * 1000;
const TOKEN_TTL_MS = 30 * 24 * 3600 * 1000;
const PAYMENT_TTL_MS = 15 * 60 * 1000;
const BATCH_NAME_TO_ID = { Morning: 1, Evening: 2 };
const DB_FILE = path.join(__dirname, "data", "db.json");
const SAVE_DEBOUNCE_MS = 150;
let saveTimer = null;

const activeOtps = new Map();
const usedOtpKeys = new Set();
const sessions = new Map();
const tokens = new Map();
let students = [], records = [], announcements = [], assignments = [], timetable = [], invoices = [], payments = [], users = [], messages = [], notifications = [];
let profiles = {};

function persist() {
  if (saveTimer) clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    saveTimer = null;
    try {
      fs.mkdirSync(path.dirname(DB_FILE), { recursive: true });
      const tmp = `${DB_FILE}.tmp`;
      fs.writeFileSync(tmp, JSON.stringify({ students, records, announcements, assignments, invoices, timetable, payments, users, messages, notifications, profiles, tokens: [...tokens.entries()], sessions: [...sessions.entries()], usedOtpKeys: [...usedOtpKeys], activeOtps: [...activeOtps.entries()] }, null, 2));
      fs.renameSync(tmp, DB_FILE);
    } catch (err) { console.error("db save failed:", err.message); }
  }, SAVE_DEBOUNCE_MS);
}
(function loadDb() {
  try {
    const raw = fs.readFileSync(DB_FILE, "utf8").replace(/^\uFEFF/, "");
    const db = JSON.parse(raw);
    if (Array.isArray(db.students)) students = db.students;
    if (Array.isArray(db.records)) records = db.records;
    if (Array.isArray(db.announcements)) announcements = db.announcements;
    if (Array.isArray(db.assignments)) assignments = db.assignments;
    if (Array.isArray(db.invoices)) invoices = db.invoices;
    if (Array.isArray(db.timetable)) timetable = db.timetable;
    if (Array.isArray(db.payments)) payments = db.payments;
    if (Array.isArray(db.users)) users = db.users;
    if (Array.isArray(db.messages)) messages = db.messages;
    if (Array.isArray(db.notifications)) notifications = db.notifications;
    if (db.profiles && typeof db.profiles === "object") profiles = db.profiles;
    if (Array.isArray(db.tokens)) for (const [k, v] of db.tokens) tokens.set(k, v);
    if (Array.isArray(db.sessions)) for (const [k, v] of db.sessions) sessions.set(k, v);
    if (Array.isArray(db.usedOtpKeys)) for (const k of db.usedOtpKeys) usedOtpKeys.add(k);
    if (Array.isArray(db.activeOtps)) for (const [k, v] of db.activeOtps) activeOtps.set(k, v);
    purgeExpiredOtps(); purgeExpiredTokens(); purgeExpiredPayments();
  } catch {}
})();

function today() { const d = new Date(); return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,"0")}-${String(d.getDate()).padStart(2,"0")}`; }
function nowIso() { return new Date().toISOString(); }
function sendJson(res, status, data) { res.writeHead(status, { "Content-Type":"application/json; charset=utf-8","Access-Control-Allow-Origin":"*","Access-Control-Allow-Methods":"GET,POST,PUT,PATCH,DELETE,OPTIONS","Access-Control-Allow-Headers":"Content-Type, Authorization","Cache-Control":"no-store" }); res.end(JSON.stringify(data)); }
function unauthorized(res) { return sendJson(res, 401, { error: "unauthorized" }); }
function normalizeDob(v) {
  const s = String(v || "").trim();
  if (!s) return "";
  const digits = s.replace(/\D/g, "");
  if (/^\d{8}$/.test(digits) && !/^\d{4}-\d{2}-\d{2}$/.test(s)) return digits; // DDMMYYYY
  if (/^\d{4}-\d{2}-\d{2}$/.test(s)) { const [y,m,d]=s.split("-"); return `${d}${m}${y}`; }
  if (/^\d{2}[/-]\d{2}[/-]\d{4}$/.test(s)) { const [d,m,y]=s.split(/[/-]/); return `${d}${m}${y}`; }
  if (/^\d{8}$/.test(digits)) return digits;
  return "";
}
function dobToDisplay(ddmmyyyy) { const s=normalizeDob(ddmmyyyy); return s.length===8 ? `${s.slice(0,2)}-${s.slice(2,4)}-${s.slice(4,8)}` : ""; }
function setUserPassword(user, password) { if (!user || !password) return false; const salt=crypto.randomBytes(16).toString("hex"); user.salt=salt; user.passwordHash=crypto.scryptSync(String(password),salt,64).toString("hex"); user.passwordChangedAt=nowIso(); user.mustChangePassword=false; return true; }
async function readBody(req) { const chunks=[]; for await (const c of req) chunks.push(c); const raw=Buffer.concat(chunks).toString("utf8"); if(!raw) return {}; try { return JSON.parse(raw); } catch { return {}; } }
function createUser(email, password, role, studentId=null, opts={}) { const e=String(email||"").trim().toLowerCase(); if(!e||!password) return null; if(users.find(u=>u.email===e)) return users.find(u=>u.email===e); const salt=crypto.randomBytes(16).toString("hex"); const passwordHash=crypto.scryptSync(String(password),salt,64).toString("hex"); const u={email:e,passwordHash,salt,role,studentId:studentId==null?null:Number(studentId),dob:normalizeDob(opts.dob),mustChangePassword:Boolean(opts.mustChangePassword),createdAt:today()}; users.push(u); persist(); return u; }
function verifyPassword(user, password) { if(!user||!password) return false; const c=crypto.scryptSync(String(password),user.salt,64).toString("hex"); try { return crypto.timingSafeEqual(Buffer.from(c,"hex"),Buffer.from(user.passwordHash,"hex")); } catch { return false; } }
function purgeExpiredTokens() { const n=Date.now(); for(const [k,t] of tokens) if(t.expiresAt<=n) tokens.delete(k); }
function purgeExpiredOtps() { const n=Date.now(); for(const [k,o] of activeOtps) if(o.expiresAt<=n) activeOtps.delete(k); }
function purgeExpiredPayments() { const n=Date.now(); for(const p of payments) if(p.status==="pending" && (n - new Date(p.createdAt||0).getTime()) > PAYMENT_TTL_MS) p.status="expired"; }
function issueToken(user) { purgeExpiredTokens(); const token=crypto.randomBytes(24).toString("hex"); tokens.set(token,{email:user.email,role:user.role,studentId:user.studentId??null,expiresAt:Date.now()+TOKEN_TTL_MS}); persist(); return token; }
function authUser(req) { const h=req.headers.authorization||""; if(!h.startsWith("Bearer ")) return null; const t=tokens.get(h.slice(7).trim()); if(!t) return null; if(t.expiresAt<=Date.now()){tokens.delete(h.slice(7).trim()); return null;} return t; }
function requireRole(req, roles) { const a=authUser(req); return a && roles.includes(a.role) ? a : null; }
function canManageStudent(auth, studentId) { if(!auth) return false; if(auth.role==="teacher") return true; return auth.studentId!=null && Number(auth.studentId)===Number(studentId); }
function effectiveProfile(auth) { const u=users.find(x=>x.email===auth.email); const p=profiles[auth.email]||{}; const fallback = auth.role==="teacher" ? (u?.name || "Teacher") : (u?.name || ""); return { email:auth.email, role:auth.role, studentId:auth.studentId??null, name:String(p.name||fallback||""), phone:String(p.phone||u?.phone||""), dob:dobToDisplay(p.dob||u?.dob||""), mustChangePassword:Boolean(u?.mustChangePassword), createdAt:u?.createdAt||null }; }
function saveProfile(auth, body) {
  const prev = profiles[auth.email] || {};
  const dob = body?.dob != null ? normalizeDob(body.dob) : (prev.dob || "");
  profiles[auth.email] = { name:String(body?.name ?? prev.name ?? "").trim().slice(0,120), phone:String(body?.phone ?? prev.phone ?? "").trim().slice(0,40), dob, updatedAt:nowIso() };
  if (dob) { const u=users.find(x=>x.email===auth.email); if(u){ u.dob=dob; } }
  persist();
  return effectiveProfile(auth);
}

function ensureSession(batchId,date,source){ const key=`${batchId}:${date}`; const ex=sessions.get(key); if(ex){ if(source==="manual") ex.source="manual"; return ex;} const s={batchId:Number(batchId),date,source}; sessions.set(key,s); return s; }
function attendancePctFor(student){ const batchId=student.batchId ?? (student.batch && BATCH_NAME_TO_ID[student.batch]) ?? null; if(batchId==null) return null; const sl=[...sessions.values()].filter(s=>s.batchId===Number(batchId)); if(!sl.length) return 0; const present=sl.filter(s=>{ const rec=records.find(r=>r.batchId===Number(batchId)&&r.studentId===Number(student.id)&&r.date===s.date); return rec && rec.status==="present"; }).length; return Math.round((present/sl.length)*100); }
function studentsWithStats(){ return students.map(s=>({...s,attendancePct:attendancePctFor(s)})); }
function findStudentById(id){ return students.find(s=>s.id===Number(id)); }
function upsertStudentAccount(student,password,parentEmail,parentPassword,opts={}){ if(!student?.email) return; let u=users.find(x=>x.email===student.email.toLowerCase()); if(!u && password) { createUser(student.email,password,"student",student.id,{dob:opts.studentDob,mustChangePassword:Boolean(opts.studentMustChange)}); u=users.find(x=>x.email===student.email.toLowerCase()); } if(u){ u.studentId=student.id; const sd=normalizeDob(opts.studentDob); if(sd) u.dob=sd; if(password){ setUserPassword(u,password); if(opts.studentMustChange!=null) u.mustChangePassword=Boolean(opts.studentMustChange); } } const pd=normalizeDob(opts.parentDob); if(parentEmail && (parentPassword || pd)) createUser(parentEmail,parentPassword||pd,"parent",student.id,{dob:pd,mustChangePassword:Boolean(parentPassword?opts.parentMustChange:pd)}); persist(); }

function listForStudent(batchId,studentId){ const rows=[]; const sl=[...sessions.values()].filter(s=>s.batchId===Number(batchId)).sort((a,b)=>a.date<b.date?1:-1); for(const s of sl){ const rec=records.find(r=>r.batchId===Number(batchId)&&r.studentId===Number(studentId)&&r.date===s.date); rows.push({date:s.date,source:s.source,status:rec?rec.status:"absent",method:rec?rec.method:null,ts:rec?rec.ts:null}); } const present=rows.filter(r=>r.status==="present").length; return {batchId:Number(batchId),studentId:Number(studentId),sessions:rows,present,absent:rows.length-present,total:rows.length,pct:rows.length?Math.round((present/rows.length)*100):0}; }
function marksForDate(batchId,date){ const marks={}, methods={}, by=new Map(); for(const r of records){ if(r.batchId!==Number(batchId)||r.date!==date) continue; if(!by.has(r.studentId)||(r.ts||"")>(by.get(r.studentId).ts||"")) by.set(r.studentId,r);} for(const r of by.values()){ marks[r.studentId]=r.status; methods[r.studentId]=r.method; } return {batchId:Number(batchId),date,marks,methods}; }
function sessionsForBatch(batchId){ return {batchId:Number(batchId), sessions:[...sessions.values()].filter(s=>s.batchId===Number(batchId)).sort((a,b)=>a.date<b.date?1:-1).map(s=>{ const br=records.filter(r=>r.batchId===s.batchId&&r.date===s.date); const present=br.filter(r=>r.status==="present").length; const batchRoster=students.filter(st=>(st.batchId??BATCH_NAME_TO_ID[st.batch]??null)===s.batchId).length; return {date:s.date,source:s.source,present,absent:Math.max(batchRoster-present,br.filter(r=>r.status==="absent").length),otpVerified:br.filter(r=>r.method==="otp").length}; })}; }

function invoiceStatus(inv){ if(inv.date) return "paid"; if(inv.dueDate && inv.dueDate < today()) return "overdue"; return "due"; }
function normalizeInvoice(inv){ return {...inv,status:invoiceStatus(inv)}; }
function listInvoices(batchId,studentId){ let rows=invoices; if(batchId) rows=rows.filter(i=>i.batchId===Number(batchId)); if(studentId) rows=rows.filter(i=>i.studentId===Number(studentId)); return rows.slice().sort((a,b)=>a.period<b.period?1:-1).map(normalizeInvoice); }
function findInvoice(id){ return invoices.find(i=>i.id===Number(id)); }
function createInvoice({studentId,batchId,batch,period,periodTa,amount,dueDate}){ if(!studentId||amount==null||amount==="") return {error:"studentId and amount are required"}; const amt=Number(amount); if(!Number.isFinite(amt)||amt<0) return {error:"invalid_amount"}; if(dueDate && !/^\d{4}-\d{2}-\d{2}$/.test(String(dueDate))) return {error:"invalid_due_date"}; const student=findStudentById(studentId); const inv={id:Date.now(),studentId:Number(studentId),studentName:student?.name||"",batchId:Number(batchId)||(batch&&BATCH_NAME_TO_ID[batch])||(student?.batchId??null),batch:batch||student?.batch||"",period:String(period||today()).slice(0,100),periodTa:String(periodTa||period||today()).slice(0,100),amount:amt,status:"due",dueDate:dueDate?String(dueDate):"",date:null,method:null,createdAt:today(),updatedAt:today()}; invoices.push(inv); persist(); return {ok:true,invoice:normalizeInvoice(inv)}; }
function updateInvoice(id,body){ const inv=findInvoice(id); if(!inv) return {error:"invoice_not_found"}; if(body.amount!=null){ const amt=Number(body.amount); if(!Number.isFinite(amt)||amt<0) return {error:"invalid_amount"}; inv.amount=amt; } if(body.period!=null) inv.period=String(body.period).slice(0,100); if(body.periodTa!=null) inv.periodTa=String(body.periodTa).slice(0,100); if(body.dueDate!=null){ if(body.dueDate!=="" && !/^\d{4}-\d{2}-\d{2}$/.test(String(body.dueDate))) return {error:"invalid_due_date"}; inv.dueDate=String(body.dueDate); } if(body.status==="paid" && !inv.date){ inv.date=today(); inv.method=inv.method||"manual"; } else if(body.status==="due"){ inv.date=null; inv.method=null; } inv.updatedAt=today(); persist(); return {ok:true,invoice:normalizeInvoice(inv)}; }
function deleteInvoice(id){ const b=invoices.length; invoices=invoices.filter(i=>i.id!==Number(id)); if(invoices.length===b) return {error:"invoice_not_found"}; payments=payments.filter(p=>p.invoiceId!==Number(id)); persist(); return {ok:true}; }
function payInvoice(id,method){ const inv=findInvoice(id); if(!inv) return {error:"invoice_not_found"}; if(inv.date) return {error:"already_paid"}; inv.date=today(); inv.method=method?String(method):"online"; inv.updatedAt=today(); const p={id:Date.now(),invoiceId:inv.id,studentId:inv.studentId,amount:inv.amount,gateway:"internal",method:inv.method,status:"confirmed",receiptNo:`R-${Date.now()}`,createdAt:nowIso(),updatedAt:nowIso()}; payments.push(p); persist(); return {ok:true,invoice:normalizeInvoice(inv),payment:p}; }

function listPayments(batchId,studentId){ purgeExpiredPayments(); let rows=payments; if(studentId) rows=rows.filter(p=>p.studentId===Number(studentId)); if(batchId){ const ids=new Set(invoices.filter(i=>i.batchId===Number(batchId)).map(i=>i.id)); rows=rows.filter(p=>ids.has(p.invoiceId)); } return rows.slice().sort((a,b)=>String(b.createdAt).localeCompare(String(a.createdAt))); }
function findPayment(id){ return payments.find(p=>p.id===Number(id)); }
function reversePayment(payment){ if(!payment) return {error:"payment_not_found"}; if(payment.status!=="confirmed") return {error:"not_confirmed"}; payment.status="reversed"; payment.updatedAt=nowIso(); const inv=findInvoice(payment.invoiceId); if(inv){ inv.date=null; inv.method=null; inv.updatedAt=today(); } persist(); return {ok:true,payment,invoice:inv?normalizeInvoice(inv):null}; }
function createUpiPayment(body){ const inv=findInvoice(body.invoiceId); if(!inv) return {error:"invoice_not_found"}; if(inv.date) return {error:"already_paid"}; const p={id:Date.now(),invoiceId:inv.id,studentId:inv.studentId,amount:inv.amount,gateway:"upi-intent",method:"UPI",status:"pending",receiptNo:null,createdAt:nowIso(),updatedAt:nowIso(),vpa:process.env.UPI_VPA||"demo@upi"}; payments.push(p); persist(); return {ok:true,payment:p}; }
function buildUpiIntent(payment){ const vpa=process.env.UPI_VPA||"demo@upi"; const name=encodeURIComponent(process.env.UPI_PAYEE_NAME||"Tuition"); return `upi://pay?pa=${encodeURIComponent(vpa)}&pn=${name}&am=${encodeURIComponent(payment.amount)}&cu=INR&tn=${encodeURIComponent("Invoice "+payment.invoiceId)}`; }

function assignmentStatus(a){ if(!a.submissions?.length) return "pending"; return a.submissions.every(s=>s.marks!=null)?"graded":"submitted"; }
function listAssignments(batchId){ const rows=(batchId?assignments.filter(a=>a.batchId===Number(batchId)):assignments).slice().sort((a,b)=>(a.id<b.id?1:-1)).map(a=>({...a,status:assignmentStatus(a)})); return {assignments:rows}; }
function createAssignment({title,batch,batchId,dueDate,maxMarks,subject}){ if(!title||!batch) return {error:"title and batch are required"}; const item={id:Date.now(),title:String(title).slice(0,200),titleTa:String(title).slice(0,200),subject:String(subject||"Mathematics"),subjectTa:String(subject||"Mathematics"),batch:String(batch),batchId:Number(batchId)||BATCH_NAME_TO_ID[String(batch)]||null,dueDate:dueDate?String(dueDate):today(),maxMarks:Number(maxMarks)||20,submissions:[]}; assignments.push(item); persist(); return {ok:true,assignment:{...item,status:"pending"}}; }
function findAssignment(id){ return assignments.find(a=>a.id===Number(id)); }
function submitAssignment({id,studentId,studentName,note}){ const a=findAssignment(id); if(!a) return {error:"assignment_not_found"}; if(!studentId) return {error:"studentId required"}; let sub=a.submissions.find(s=>s.studentId===Number(studentId)); if(!sub){ sub={studentId:Number(studentId),studentName:studentName||"",note:"",submittedOn:today(),marks:null,feedback:null}; a.submissions.push(sub);} sub.note=note==null?sub.note:String(note).slice(0,2000); persist(); return {ok:true,assignmentId:a.id,submission:sub}; }
function gradeAssignment({id,studentId,marks,feedback}){ const a=findAssignment(id); if(!a) return {error:"assignment_not_found"}; const sub=a.submissions.find(s=>s.studentId===Number(studentId)); if(!sub) return {error:"submission_not_found"}; if(marks!=null){ const m=Number(marks); if(!Number.isFinite(m)) return {error:"invalid_marks"}; sub.marks=m; } sub.feedback=feedback==null?sub.feedback:String(feedback).slice(0,2000); persist(); return {ok:true,assignmentId:a.id,submission:sub,status:assignmentStatus(a)}; }

function listTimetable(batchId){ return {timetable:timetable.filter(c=>batchId?c.batchId===Number(batchId):true).slice().sort((a,b)=>a.day-b.day||(a.start<b.start?-1:1))}; }
function saveTimetableClass({id,batchId,day,subject,start,end,mode,teacher}){ const batch=Number(batchId); if(!batch||!subject||!start||!end) return {error:"batchId, subject, start, end required"}; const item={id:id?Number(id):Date.now(),batchId:batch,day:Math.min(6,Math.max(0,Number(day)||0)),subject:String(subject).trim().slice(0,120),start:String(start),end:String(end),mode:mode==="online"?"online":"offline",teacher:teacher?String(teacher).slice(0,120):""}; const idx=timetable.findIndex(c=>c.id===item.id); if(idx>=0) timetable[idx]=item; else timetable.push(item); persist(); return {ok:true,entry:item}; }
function removeTimetableClass(id){ const b=timetable.length; timetable=timetable.filter(c=>c.id!==Number(id)); if(timetable.length===b) return {error:"not_found"}; persist(); return {ok:true}; }

function listAnnouncements(){ return {announcements:[...announcements].sort((a,b)=>(a.id<b.id?1:-1))}; }
function createAnnouncement({title,body}){ if(!title||!body) return null; const item={id:Date.now(),title:String(title).slice(0,200),titleTa:String(title).slice(0,200),body:String(body).slice(0,5000),bodyTa:String(body).slice(0,5000),date:today()}; announcements.push(item); persist(); return item; }

function listMessagesFor(auth, studentId){ if(auth.role==="teacher"){ if(!studentId) return {threads:[]}; return {messages:messages.filter(m=>m.studentId===Number(studentId)).sort((a,b)=>a.id-b.id)}; } return {messages:messages.filter(m=>m.studentId===Number(auth.studentId)).sort((a,b)=>a.id-b.id)}; }
function postMessage(auth, body){ const sid = auth.role==="teacher"?Number(body?.studentId):Number(auth.studentId); if(!sid || !String(body?.body||"").trim()) return {error:"studentId and body required"}; if(auth.role!=="teacher" && Number(auth.studentId)!==sid) return {error:"forbidden"}; const msg={id:Date.now(),studentId:sid,fromRole:auth.role,fromName:String(body?.fromName||auth.email),fromEmail:auth.email,body:String(body.body).trim().slice(0,5000),createdAt:nowIso(),read:false}; messages.push(msg); persist(); return {ok:true,message:msg}; }
function messageThread(auth, studentId, markRead){ const rows=messages.filter(m=>m.studentId===Number(studentId)).sort((a,b)=>a.id-b.id); if(markRead){ for(const m of rows) if(m.fromRole!==auth.role) m.read=true; persist(); } return rows; }
function listNotificationsFor(auth){ const rows=notifications.filter(n=>n.audience==="all"||n.audience===auth.role||(n.studentId!=null && n.studentId===auth.studentId)); return {notifications:rows.slice().sort((a,b)=>(b.id<a.id?1:-1))}; }
function createNotification({audience,studentId,title,body}){ if(!title) return null; const item={id:Date.now(),audience:audience||"all",studentId:studentId==null?null:Number(studentId),title:String(title).slice(0,200),titleTa:String(title).slice(0,200),body:String(body||"").slice(0,5000),bodyTa:String(body||"").slice(0,5000),date:today(),read:false}; notifications.push(item); return item; }
function markNotificationsRead(auth, ids){ const list=Array.isArray(ids)?new Set(ids.map(Number)):null; let marked=0; for(const n of notifications){ if(!(n.audience==="all"||n.audience===auth.role||(n.studentId!=null&&n.studentId===auth.studentId))) continue; if(list && !list.has(n.id)) continue; if(!n.read){ n.read=true; marked++; } } persist(); return {ok:true,marked}; }

function generateOtp(batchId){ if(!batchId) return {error:"batchId required"}; purgeExpiredOtps(); const code=String(Math.floor(100000+Math.random()*900000)); const now=Date.now(); activeOtps.set(`${Number(batchId)}:${code}`,{code,batchId:Number(batchId),createdAt:now,expiresAt:now+OTP_TTL_MS}); ensureSession(Number(batchId),today(),"otp"); persist(); return {batchId:Number(batchId),code,expiresAt:now+OTP_TTL_MS,ttlMs:OTP_TTL_MS}; }
function verifyOtp({batchId,studentId,studentName,code}){ if(!code||!studentId) return {error:"studentId and code are required"}; const date=today(); let otp=activeOtps.get(`${batchId}:${code}`); if(!otp){ for(const o of activeOtps.values()) if(o.code===code){ otp=o; break; } } if(!otp) return {error:"wrong_code"}; batchId=otp.batchId; if(otp.expiresAt<=Date.now()){ activeOtps.delete(`${batchId}:${code}`); return {error:"expired"}; } if(usedOtpKeys.has(`${batchId}:${date}:${code}:${studentId}`)) return {error:"already_used"}; const existing=records.find(r=>r.batchId===Number(batchId)&&r.studentId===Number(studentId)&&r.date===date); if(existing && existing.method==="otp") return {error:"already_marked"}; if(existing && existing.method==="manual") records=records.filter(r=>!(r.batchId===Number(batchId)&&r.studentId===Number(studentId)&&r.date===date&&r.method==="manual")); records.push({batchId:Number(batchId),studentId:Number(studentId),studentName:studentName||"",date,status:"present",method:"otp",ts:nowIso()}); usedOtpKeys.add(`${batchId}:${date}:${code}:${studentId}`); ensureSession(Number(batchId),date,"otp"); persist(); return {ok:true,date,status:"present",code}; }
function saveManual({batchId,date,marks}){ if(!batchId||!date||!marks||typeof marks!=="object") return {error:"batchId, date and marks object are required"}; records=records.filter(r=>!(r.batchId===Number(batchId)&&r.date===date&&r.method==="manual")); for(const [studentId,status] of Object.entries(marks)) records.push({batchId:Number(batchId),studentId:Number(studentId),studentName:"",date,status:status==="absent"?"absent":"present",method:"manual",ts:nowIso()}); ensureSession(Number(batchId),date,"manual"); persist(); return {ok:true,saved:records.filter(r=>r.batchId===Number(batchId)&&r.date===date).length,date}; }

function createPayment({invoiceId,gateway,method}){ const inv=findInvoice(invoiceId); if(!inv) return {error:"invoice_not_found"}; if(inv.date) return {error:"already_paid"}; const p={id:Date.now(),invoiceId:inv.id,studentId:inv.studentId,amount:inv.amount,gateway:gateway||"internal",method:method||(gateway==="upi-intent"?"UPI":"online"),status:"pending",receiptNo:null,createdAt:nowIso(),updatedAt:nowIso()}; payments.push(p); persist(); return {ok:true,payment:p}; }
function confirmPayment(paymentId,method){ const p=findPayment(paymentId); if(!p) return {error:"payment_not_found"}; if(p.status==="confirmed") return {ok:true,payment:p,invoice:normalizeInvoice(findInvoice(p.invoiceId))}; const inv=findInvoice(p.invoiceId); if(!inv) return {error:"invoice_not_found"}; p.status="confirmed"; p.method=method||p.method||"online"; p.receiptNo=p.receiptNo||`R-${Date.now()}`; p.updatedAt=nowIso(); inv.date=today(); inv.method=p.method; inv.updatedAt=today(); persist(); return {ok:true,payment:p,invoice:normalizeInvoice(inv)}; }

const server = http.createServer(async (req, res) => {
  try {
    if (req.method === "OPTIONS") return sendJson(res, 204, {});
    const url = new URL(req.url, `http://${req.headers.host || "localhost"}`);
    const p = url.pathname.replace(/\/+$/, "") || "/";
    const q = Object.fromEntries(url.searchParams.entries());
    const body = (req.method === "POST" || req.method === "PUT" || req.method === "PATCH") ? await readBody(req) : {};

    if (req.method === "GET" && p === "/api/health") return sendJson(res, 200, { ok: true, name: "attendance-server", otpTtlMs: OTP_TTL_MS });
    if (req.method === "GET" && p === "/api/config") return sendJson(res, 200, { razorpayEnabled: Boolean(process.env.RAZORPAY_KEY_ID && process.env.RAZORPAY_KEY_SECRET), upiIntentEnabled: Boolean(process.env.UPI_VPA) });

    // Auth
    if (req.method === "POST" && p === "/api/auth/login") {
      const email = String(body.email || "").trim().toLowerCase();
      const password = String(body.password || "");
      let user = users.find((u) => u.email === email);
      // First-run teacher bootstrap: when no teacher account exists, the first
      // @kkta.ac.in login creates the teacher account using the entered password.
      if (!user && email.endsWith("@kkta.ac.in") && !users.some((u) => u.role === "teacher") && password) {
        user = createUser(email, password, "teacher", null, { mustChangePassword: false });
      }
      if (!user || !verifyPassword(user, password)) return sendJson(res, 401, { error: "invalid_credentials" });
      const token = issueToken(user);
      return sendJson(res, 200, { ok: true, token, user: { email: user.email, role: user.role, studentId: user.studentId ?? null, mustChangePassword: Boolean(user.mustChangePassword) } });
    }
    if (req.method === "GET" && p === "/api/auth/me") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const user = effectiveProfile(auth);
      const student = user.studentId != null ? studentsWithStats().find((s) => s.id === Number(user.studentId)) : null;
      return sendJson(res, 200, { ok: true, user, student });
    }
    if (req.method === "POST" && p === "/api/auth/logout") {
      const h = req.headers.authorization || ""; if (h.startsWith("Bearer ")) { tokens.delete(h.slice(7).trim()); persist(); }
      return sendJson(res, 200, { ok: true });
    }
    if (req.method === "GET" && p === "/api/profile") { const auth = authUser(req); if (!auth) return unauthorized(res); return sendJson(res, 200, { ok: true, user: effectiveProfile(auth) }); }
    if (req.method === "PUT" && p === "/api/profile") { const auth = authUser(req); if (!auth) return unauthorized(res); return sendJson(res, 200, { ok: true, user: saveProfile(auth, body) }); }
    if (req.method === "POST" && p === "/api/profile/password") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const user = users.find((u) => u.email === auth.email); if (!user) return unauthorized(res);
      const next = String(body.newPassword || body.password || "");
      if (next.length < 6) return sendJson(res, 400, { error: "password_too_short", message: "Password must be at least 6 characters" });
      if (!user.mustChangePassword && !verifyPassword(user, body.currentPassword)) return sendJson(res, 400, { error: "invalid_current_password", message: "Current password is incorrect" });
      setUserPassword(user, next); persist();
      return sendJson(res, 200, { ok: true, user: effectiveProfile(auth) });
    }

    // Students
    if (p === "/api/students" && req.method === "GET") {
      const auth = authUser(req);
      if (auth && auth.role !== "teacher" && auth.studentId != null) {
        const s = studentsWithStats().find((x) => x.id === Number(auth.studentId));
        return sendJson(res, 200, s ? [s] : []);
      }
      if (auth) return sendJson(res, 200, studentsWithStats());
      // Unauthenticated callers (developer dashboard) get no contact details
      return sendJson(res, 200, studentsWithStats().map(({ email, contact, dob, ...rest }) => rest));
    }
    if (p === "/api/students" && req.method === "POST") {
      const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res);
      const email = String(body.email || "").trim().toLowerCase();
      const studentDob = normalizeDob(body.studentDob || body.dob);
      if (!body.name || !String(body.name).trim()) return sendJson(res, 400, { error: "name_required", message: "Name is required" });
      if (email && users.some((u) => u.email === email)) return sendJson(res, 409, { error: "email_taken", message: "An account already exists for that email" });
      const studentPassword = String(body.password || "").trim() || studentDob; // default password = DOB (DDMMYYYY) if no explicit password
      if (email && !studentPassword) return sendJson(res, 400, { error: "password_required", message: "Set a student login password or student DOB (DDMMYYYY)" });
      const batch = String(body.batch || "Evening");
      const student = { id: students.length ? Math.max(...students.map((s) => s.id)) + 1 : 1, name: String(body.name).trim().slice(0,120), batch, batchId: BATCH_NAME_TO_ID[batch] || Number(body.batchId) || null, contact: String(body.contact || "").trim().slice(0,40), email: email || undefined, dob: dobToDisplay(studentDob), createdAt: today() };
      students.push(student);
      if (email) upsertStudentAccount(student, studentPassword, body.parentEmail, body.parentPassword, { studentDob, parentDob: body.parentDob, studentMustChange: Boolean(studentDob && !String(body.password || "").trim()), parentMustChange: Boolean(normalizeDob(body.parentDob) && !String(body.parentPassword || "").trim()) });
      persist();
      return sendJson(res, 201, student);
    }
    const studentMatch = p.match(/^\/api\/students\/(\d+)$/);
    if (studentMatch) {
      const sid = Number(studentMatch[1]);
      if (req.method === "GET") { const s = studentsWithStats().find((x)=>x.id===sid); return s ? sendJson(res,200,s) : sendJson(res,404,{error:"not_found"}); }
      if (req.method === "PUT" || req.method === "PATCH") {
        const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res);
        const s = findStudentById(sid); if (!s) return sendJson(res,404,{error:"not_found"});
        if (body.name != null) s.name = String(body.name).trim().slice(0,120);
        if (body.batch != null) { s.batch = String(body.batch); s.batchId = BATCH_NAME_TO_ID[s.batch] || s.batchId; }
        if (body.contact != null) s.contact = String(body.contact).trim().slice(0,40);
        if (body.email != null) s.email = String(body.email).trim().toLowerCase() || undefined;
        persist(); return sendJson(res,200,s);
      }
      if (req.method === "DELETE") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const b=students.length; students=students.filter((s)=>s.id!==sid); if(students.length===b) return sendJson(res,404,{error:"not_found"}); persist(); return sendJson(res,200,{ok:true}); }
    }

    // Attendance / OTP
    if (req.method === "GET" && p === "/api/attendance") {
      const batchId = Number(q.batchId), date = String(q.date || today());
      if (!batchId) return sendJson(res, 400, { error: "batchId required" });
      return sendJson(res, 200, marksForDate(batchId, date));
    }
    if (req.method === "POST" && p === "/api/attendance/manual") {
      const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res);
      return sendJson(res, 200, saveManual(body));
    }
    if (req.method === "POST" && p === "/api/otp/generate") {
      const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res);
      const out = generateOtp(body.batchId); return sendJson(res, out.error ? 400 : 200, out);
    }
    if (req.method === "POST" && p === "/api/otp/verify") {
      const out = verifyOtp(body); return sendJson(res, out.error ? 400 : 200, out);
    }
    if (req.method === "GET" && p === "/api/attendance/student") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const out = listForStudent(Number(q.batchId), Number(q.studentId)); return sendJson(res, 200, out);
    }
    if (req.method === "GET" && p === "/api/attendance/sessions") return sendJson(res, 200, sessionsForBatch(Number(q.batchId)));

    // Invoices
    if (p === "/api/invoices" && req.method === "GET") {
      const auth = authUser(req);
      const sid = q.studentId ? Number(q.studentId) : (auth && auth.role !== "teacher" ? auth.studentId : null);
      // Unauthenticated callers (developer dashboard) get masked names
      if (!auth) return sendJson(res, 200, { invoices: listInvoices(q.batchId, sid).map(({ studentName, batch, ...rest }) => rest) });
      return sendJson(res, 200, { invoices: listInvoices(q.batchId, sid) });
    }
    if (p === "/api/invoices" && req.method === "POST") {
      const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res);
      const out = createInvoice(body); return sendJson(res, out.error ? 400 : 201, out);
    }
    const invMatch = p.match(/^\/api\/invoices\/(\d+)(?:\/(pay))?$/);
    if (invMatch) {
      const id = Number(invMatch[1]);
      if (invMatch[2] === "pay" && req.method === "POST") {
        const auth = authUser(req); if (!auth) return unauthorized(res);
        const out = payInvoice(id, body.method); return sendJson(res, out.error ? 400 : 200, out);
      }
      if (req.method === "PUT" || req.method === "PATCH") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const out = updateInvoice(id, body); return sendJson(res, out.error ? 400 : 200, out); }
      if (req.method === "DELETE") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const out = deleteInvoice(id); return sendJson(res, out.error ? 400 : 200, out); }
      if (req.method === "GET") { const inv = findInvoice(id); return inv ? sendJson(res,200,normalizeInvoice(inv)) : sendJson(res,404,{error:"not_found"}); }
    }

    // Payments
    if (p === "/api/payments" && req.method === "GET") {
      const auth = authUser(req); const sid = q.studentId ? Number(q.studentId) : (auth && auth.role !== "teacher" ? auth.studentId : null);
      return sendJson(res, 200, { payments: listPayments(q.batchId, sid) });
    }
    if (p === "/api/payments/create" && req.method === "POST") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const out = createPayment(body);
      if (out.error) return sendJson(res, 400, out);
      // Internal gateway: auto-confirm for demo/local flow
      if ((body.gateway || "internal") === "internal") return sendJson(res, 200, confirmPayment(out.payment.id, body.method));
      return sendJson(res, 200, out);
    }
    if (p === "/api/payments/razorpay/order" && req.method === "POST") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      if (!(process.env.RAZORPAY_KEY_ID && process.env.RAZORPAY_KEY_SECRET)) return sendJson(res, 400, { error: "razorpay_not_configured" });
      const inv = findInvoice(body.invoiceId); if (!inv) return sendJson(res, 404, { error: "invoice_not_found" }); if (inv.date) return sendJson(res, 400, { error: "already_paid" });
      const p = createPayment({ invoiceId: inv.id, gateway: "razorpay", method: "razorpay" }).payment;
      return sendJson(res, 200, { ok: true, paymentId: p.id, orderId: `order_local_${p.id}`, keyId: process.env.RAZORPAY_KEY_ID, amount: Math.round(Number(inv.amount) * 100), currency: "INR" });
    }
    if (p === "/api/payments/razorpay/verify" && req.method === "POST") {
      const p = findPayment(body.paymentId); if (!p) return sendJson(res, 404, { error: "payment_not_found" });
      if (process.env.RAZORPAY_KEY_SECRET && body.razorpay_order_id && body.razorpay_payment_id && body.razorpay_signature) {
        const expected = crypto.createHmac("sha256", process.env.RAZORPAY_KEY_SECRET).update(`${body.razorpay_order_id}|${body.razorpay_payment_id}`).digest("hex");
        if (expected !== body.razorpay_signature) return sendJson(res, 400, { error: "signature_mismatch" });
      }
      const out = confirmPayment(p.id, "razorpay"); out.payment.gatewayOrderId = body.razorpay_order_id || null; out.payment.gatewayPaymentId = body.razorpay_payment_id || null; persist();
      return sendJson(res, 200, out);
    }
    if (p === "/api/payments/upi/create" && req.method === "POST") { const auth = authUser(req); if (!auth) return unauthorized(res); const out = createUpiPayment(body); if (out.error) return sendJson(res, 400, out); return sendJson(res, 200, { ...out, intent: buildUpiIntent(out.payment) }); }
    const payMatch = p.match(/^\/api\/payments\/(\d+)(?:\/(refund|confirm))?$/);
    if (payMatch) {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const pay = findPayment(payMatch[1]); if (!pay) return sendJson(res, 404, { error: "payment_not_found" });
      if (payMatch[2] === "refund" && req.method === "POST") { const tauth = requireRole(req, ["teacher"]); if (!tauth) return sendJson(res, 403, { error: "forbidden" }); const out = reversePayment(pay); return sendJson(res, out.error ? 400 : 200, out); }
      if (payMatch[2] === "confirm" && req.method === "POST") { const out = confirmPayment(pay.id, body.method); return sendJson(res, out.error ? 400 : 200, out); }
      if (req.method === "GET") return sendJson(res, 200, pay);
    }

    // Assignments
    if (p === "/api/assignments" && req.method === "GET") return sendJson(res, 200, listAssignments(q.batchId));
    if (p === "/api/assignments" && req.method === "POST") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const out = createAssignment(body); return sendJson(res, out.error ? 400 : 201, out); }
    const asgMatch = p.match(/^\/api\/assignments\/(\d+)(?:\/(submit|grade))?$/);
    if (asgMatch) {
      const id = Number(asgMatch[1]);
      if (asgMatch[2] === "submit" && req.method === "POST") {
        const auth = authUser(req);
        if (!auth || !canManageStudent(auth, body.studentId)) return unauthorized(res);
        return sendJson(res, 200, submitAssignment({ ...body, id }));
      }
      if (asgMatch[2] === "grade" && req.method === "POST") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); return sendJson(res, 200, gradeAssignment({ ...body, id })); }
      if (req.method === "GET") { const a = findAssignment(id); return a ? sendJson(res,200,{...a,status:assignmentStatus(a)}) : sendJson(res,404,{error:"not_found"}); }
      if (req.method === "DELETE") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const b=assignments.length; assignments=assignments.filter((a)=>a.id!==id); if(assignments.length===b) return sendJson(res,404,{error:"not_found"}); persist(); return sendJson(res,200,{ok:true}); }
    }

    // Timetable
    if (p === "/api/timetable" && req.method === "GET") return sendJson(res, 200, listTimetable(q.batchId));
    if (p === "/api/timetable" && req.method === "POST") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const out = saveTimetableClass(body); return sendJson(res, out.error ? 400 : 200, out); }
    const ttMatch = p.match(/^\/api\/timetable\/(\d+)$/);
    if (ttMatch && req.method === "DELETE") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const out = removeTimetableClass(ttMatch[1]); return sendJson(res, out.error ? 400 : 200, out); }

    // Announcements
    if (p === "/api/announcements" && req.method === "GET") return sendJson(res, 200, listAnnouncements());
    if (p === "/api/announcements" && req.method === "POST") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const item = createAnnouncement(body); return item ? sendJson(res, 201, { ok: true, announcement: item }) : sendJson(res, 400, { error: "title and body required" }); }
    const annMatch = p.match(/^\/api\/announcements\/(\d+)$/);
    if (annMatch && req.method === "DELETE") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const b=announcements.length; announcements=announcements.filter((a)=>a.id!==Number(annMatch[1])); if(announcements.length===b) return sendJson(res,404,{error:"not_found"}); persist(); return sendJson(res,200,{ok:true}); }

    // Messages
    if (p === "/api/messages" && req.method === "GET") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      if (auth.role === "teacher" && q.studentId) return sendJson(res, 200, { thread: { studentId: Number(q.studentId), messages: messageThread(auth, Number(q.studentId), false) } });
      return sendJson(res, 200, listMessagesFor(auth, q.studentId));
    }
    if (p === "/api/messages" && req.method === "POST") { const auth = authUser(req); if (!auth) return unauthorized(res); const out = postMessage(auth, body); return sendJson(res, out.error ? 400 : 201, out); }
    if (p === "/api/messages/read" && req.method === "POST") {
      const auth = authUser(req); if (!auth) return unauthorized(res);
      const sid = Number(body.studentId || auth.studentId);
      if (auth.role !== "teacher" && sid !== Number(auth.studentId)) return sendJson(res, 403, { error: "forbidden" });
      return sendJson(res, 200, { ok: true, thread: { studentId: sid, messages: messageThread(auth, sid, true) } });
    }

    // Notifications
    if (p === "/api/notifications" && req.method === "GET") { const auth = authUser(req); if (!auth) return unauthorized(res); return sendJson(res, 200, listNotificationsFor(auth)); }
    if (p === "/api/notifications" && req.method === "POST") { const auth = requireRole(req, ["teacher"]); if (!auth) return unauthorized(res); const item = createNotification(body); return item ? (persist(), sendJson(res, 201, { ok: true, notification: item })) : sendJson(res, 400, { error: "title required" }); }
    if (p === "/api/notifications/read" && req.method === "POST") { const auth = authUser(req); if (!auth) return unauthorized(res); return sendJson(res, 200, markNotificationsRead(auth, body.ids)); }

    return sendJson(res, 404, { error: "not_found", path: p, method: req.method });
  } catch (err) {
    console.error(err);
    return sendJson(res, 500, { error: "server_error", message: String(err && err.message || err) });
  }
});

server.listen(PORT, () => {
  console.log(`attendance-server listening on http://localhost:${PORT} (OTP valid ${OTP_TTL_MS / 1000}s)`);
});
