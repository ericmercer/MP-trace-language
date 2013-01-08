import java.io.*;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.regex.Pattern;






public class Encoding {
String TYPE = "(declare-datatypes (T1 T2 T3 T4 T5)\n " +
		"((Recv (mk-recv (match T1) (ep T2) (var T3) (event T4) (nearestwait T5)))))\n" +
		"(declare-datatypes (T1 T2 T3 T4)\n" +
		"((Send (mk-send (match T1) (ep T2) (value T3) (event T4)))))\n" +
		"(define-fun HB ((a Int) (b Int)) Bool\n" +
		"  (if(< a b)\n" +
		" true\n" +
		" false))\n";
String MATCH = "(define-fun MATCH ((r (Recv Int Int Int Int Int)) (s (Send Int Int Int Int))) Bool\n" +
  "(if(and (= (ep r) (ep s)) (= (var r) (value s))\n" + 
    "(HB (event s) (nearestwait r)) (= (match r) (event s))\n" + 
    "(= (match s) (event r)))\n" +
    "true\n" +
    "false\n" +
  ")\n" +
")\n";

String fileinput;
String fileoutput;

String def = "";
String mdef = "";
String match = "";
String asserts = "";
String hb = "";

int N = 0;//need to be initialized 

match mc;
Hashtable<String, String> nearestWaits;
HashSet<String> variableSet;

FileInputStream fstream;
FileOutputStream fostream;
// Get the object of DataInputStream
DataInputStream in;
DataOutputStream out;
BufferedReader br;
BufferedWriter bw;

boolean debug = true;
boolean debug2 = true;

Encoding(String finput, String foutput,int threadNum){
   fileinput = finput;
   fileoutput = foutput;
   N = threadNum;
}

void ExtractSnd(int myep, String statement, String event ){
	//String op = statement.split("\\(")[0];
	String ep = statement.split("\\(|,|\\)| ")[1];
	String value = statement.split("\\(|,|\\)| ")[3];
	if(debug){
		System.out.println("value in ExtractSnd: " + value);
	}
	String name = "send"+event;

	mdef += "(declare-const " + name + " (Send Int Int Int Int))\n(assert (and (= (ep " + name + ") "
	+ ep + ") (= (event " + name + ") " + event + ") (= (value " + name + ") " + value + ")))\n";
	
	//generate send list for match pair and add HB for sends with the same endpoint
	match.send newsend = mc.createSend(name, mc.sendlist[Integer.parseInt(ep)][myep].size());
	mc.sendlist[Integer.parseInt(ep)][myep].add(newsend);
	
	if(mc.sendlist[Integer.parseInt(ep)][myep].size() > 1){
		match.send lastsend = mc.sendlist[Integer.parseInt(ep)][myep].get(mc.sendlist[Integer.parseInt(ep)][myep].size()-2);
		hb += "(HB " + lastsend.exp.substring(4) + " " + newsend.exp.substring(4) + ") ";
	}
	
}

void ExtractRecv(int ep, String statement, String event){

	String var = statement.split("\\(|,|\\)| ")[3];
	if(!variableSet.contains(var)){
		//currently, only integer is supported as basic type of variables in the encoding
		def += "(declare-const " + var +" Int)\n";
		variableSet.add(var);
	}
		
	if(debug){
		System.out.println("variable in ExtractRecv: " + var);
	}
	String name = "recv"+event;
	String des = ") (= (select " + name;
	
	
	
	mdef += "(declare-const " + name + " (Recv Int Int Int Int Int))\n(assert (and (= (ep " + name + ") " 
			+ ep + ") (= (event " + name + ") " + event + ") (= (var " + name + ") " + var + ")))\n";
	
	//generate recv list for match pair and add HB for recvs
	match.recv newrecv = mc.createRecv(name, mc.recvlist[ep].size(),event);
	mc.recvlist[ep].add(newrecv);
	
	if(mc.recvlist[ep].size() > 1){
		match.recv lastrecv = mc.recvlist[ep].get(mc.recvlist[ep].size()-2);
		//use substring because we record name, which is recv/send followed by the event
		hb += "(HB " + lastrecv.exp.substring(4) + " " + newrecv.exp.substring(4) + ") ";
	}
}

void ExtractWait(int ep, String statement, String event){
	String event_r = statement.split("\\(|\\)")[1];
	if(debug)
		System.out.println(event+": event for recv in ExtractWait: " + event_r);
	//first, check if event_r exists in recvlist
	Iterator<match.recv> ite_r = mc.recvlist[ep].iterator();
	boolean exists = false;
	while(ite_r.hasNext()){
		match.recv r = ite_r.next();
		if(r.event.equals(event_r)){
			exists = true;
			break;
		}
	}
	//second, add in the hashtable the nearest wait for all the previous recvs before event_r IF the recv has no wait yet
	//if event_r has already been assigned a wait, NO HB for event_r and wait added; otherwise, add the HB
	if(exists){
		//add nearest in the recv record for matching
		mdef += "(assert (= (nearestwait recv" + event_r + ") " + event + "))\n"; 
		
		ite_r = mc.recvlist[ep].iterator();
		while(ite_r.hasNext()){
			match.recv r = ite_r.next();
			
			if(r.event.equals(event_r)){
				//first check if event_r itself has been assigned wait
				if(!nearestWaits.containsKey(event_r)){
					if(debug)
						System.out.println("event_r is not in nearestWaits of ExtractWaits: " + event_r);
					//second, if not, add an HB for event_r and its wait
					hb += "(HB " + event_r + " " + event +") ";
					nearestWaits.put(r.event, event);
				}
				break;//end loop if we witness event_r
			}else if(!nearestWaits.containsKey(r.event)){//if the recv has not been assigned a wait
					nearestWaits.put(r.event, event);
				}
		}
	}
}


void ExtractAssumeAssert(int ep, String statement){
	//need to negate the assert, will do it in the future...
	//naively take the substring of the assert or assume
	String content = statement.substring(6);
	if(debug){
		System.out.println("statement in ExtractAssumeAssert: " + content);
	}
	ExtractVariable(content);
	asserts += "(assert " + content + ")\n";
	/*String[] variables = statement.split("\\(|\\)| |\\+|-|\\*|/|^|%|[0-9]+");//????
	for(String var : variables){
		if(!variableSet.contains(var)){
			def += "(define " + var +"::int)\n";
			variableSet.add(var); 
		}
	}*/
}

void ExtractVariable(String st){
	
	String regx = "\\(|\\)|\\+|-|\\*|/|=|<|>|^|%|\\s";
	String[] subst = st.split(regx);
	for(String var : subst){
		//if the string is integer, igore, otherwise add variable. Other basic type are not supported
		if(Pattern.matches("\\d+", var))
			continue;
		if(!variableSet.contains(var)&&!var.equals("")
				&&!var.equals("and")&&!var.equals("or")&&!var.equals("not")){
			//currently, only integer is supported as basic type of variables in the encoding
			def += "(declare-const " + var +" Int)\n";
			variableSet.add(var);
		}
	}
}

void Extract(String s){
	if(debug)
		System.out.println("source: " + s);
	String source = s;
	String[] substring = source.split(": ");
	if(debug){
		for(int i =0;i<substring.length;i++)
			System.out.println("substring["+i+"]: " + substring[i]);
	}
	String event = substring[0];
	def += "(declare-const " + event + " Int)\n";
	int endpoint = Integer.parseInt(substring[0].split("T|_")[1].trim());
	
	if(debug)
		System.out.println("endpoint in Extract: " + endpoint);
	
	if(endpoint < 0 || endpoint > N-1){
		System.out.println("error for node number: " + endpoint);
		return;
	}
	
	String op = substring[1].split("\\(")[0];
	String st = substring[1];
	
	if(debug){
		System.out.println("operation in Extract: " + op);
	}
	
	if(op.equals("snd")){
		ExtractSnd(endpoint, st, event);
	}
	else if(op.equals("rcv")){
		ExtractRecv(endpoint, st, event);
	}
	else if(op.equals("assume")||op.equals("assert")){
		ExtractAssumeAssert(endpoint, st);
	}
	else if(op.equals("wait")){
		ExtractWait(endpoint, st, event);
	}
	else{
		System.out.println("error extraction: " + source);
		return;
	}
	
}

void GenerateEncoding() throws IOException{
	hb = "(assert (and\n";
	match = "(assert (and\n";
	fstream = new FileInputStream(fileinput);
	in = new DataInputStream(fstream);
	br = new BufferedReader(new InputStreamReader(in));
	String line;
	
	mc = new match(N);
	nearestWaits = new Hashtable<String,String>();
	variableSet = new HashSet<String>();
	
	while((line = br.readLine()) != null){
		//System.out.println("line: " + line);
		Extract(line);
	}
	
	
	
	if(debug2){
		for(int i = 0; i < mc.recvlist.length; i++){
			Iterator<match.recv> ite_r = mc.recvlist[i].iterator();
			while(ite_r.hasNext()){
				match.recv r = ite_r.next();
				System.out.println("recv event and rank for recvlist["+i+"]: " + r.exp + ", " + r.rank);			
			}
		}
		
		for(int i = 0; i < mc.sendlist.length; i++){
			for(int j = 0; j < mc.sendlist[i].length; j++){
				Iterator<match.send> ite_ss = mc.sendlist[i][j].iterator();
				while(ite_ss.hasNext()){
					match.send s = ite_ss.next();
					System.out.println("send event and rank for sendlist[" + i + "][" + j + "]: " + s.exp + ", " + s.rank);
				}
			}
		}
	}
	
	
	hb += "))\n\n";
	
	//generate matches
	mc.generateMatch();
	Hashtable<String, LinkedList<String>> matchtable = mc.match_table;
	
	if(matchtable.isEmpty()){
		System.out.println("Error: No match pairs!");
		return;
	}
	
	for(String key : matchtable.keySet()){
		if(debug)
			System.out.println("key in matchtable: " + key);
		LinkedList<String> sends = matchtable.get(key);
		match += "(or ";
		Iterator<String> ite_s = sends.iterator();
		while(ite_s.hasNext()){
			String send = ite_s.next();
			match += "(MATCH " + key + " " + send + ") "; 
		}
		match += ")\n";
	}
	match += "))\n";
	
	in.close();
	fostream = new FileOutputStream(fileoutput);
    out = new DataOutputStream(fostream);
    bw = new BufferedWriter(new OutputStreamWriter(out));
    bw.write(TYPE + "\n" + MATCH + "\n" + def + "\n" + mdef + "\n" + hb + "\n" + match + "\n" + asserts + "\n(check-sat)\n");
    bw.close();
}

public static void main(String[] args)throws IOException{
	Encoding encoding = new Encoding(args[0], args[1], Integer.parseInt(args[2])/*"trace_perftest_pktuse_512.txt","perftest_pktuse_512.smt2",5*/);
	encoding.GenerateEncoding();
}

}
