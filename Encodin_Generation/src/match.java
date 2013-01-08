import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;


public class match {

public LinkedList<recv>[] recvlist;
public LinkedList<send>[][] sendlist;
public Hashtable<String, LinkedList<String>> match_table;

public match(int threadNum){
	recvlist = new LinkedList[threadNum];
	for(int i = 0; i < threadNum; i++){
		recvlist[i] = new LinkedList<recv>();
	}
	sendlist = new LinkedList[threadNum][threadNum];
	for(int i = 0; i < threadNum; i++){
		for(int j = 0; j < threadNum; j++){
			sendlist[i][j] = new LinkedList<send>();
		}
	}
	match_table = new Hashtable<String, LinkedList<String>>();
}

public send createSend(String e, int r){
	return new send(e, r);
}

public recv createRecv(String ex, int r, String e){
	return new recv(ex, r, e);
}

public void generateMatch(){
	 for(int i = 0; i < recvlist.length; i ++){
		 Iterator<recv> ite_r = recvlist[i].iterator();
		 
		 //calculate # of sends from any source to i
		 int sendstoi = 0;
		 for(int j = 0; j < sendlist[i].length; j++){
			 sendstoi += sendlist[i][j].size();
		 }
		 
		 while(ite_r.hasNext()){
			 recv r = ite_r.next();
			 
			//	 System.out.println("recv in thread i = " + i + ": " + r.exp +" with rank " + r.rank);
			 LinkedList<String> sendlistforR = new LinkedList<String>();
			 for(int j = 0; j < sendlist[i].length; j++){
				 Iterator<send> ite_s = sendlist[i][j].iterator();
				 while(ite_s.hasNext()){
					 send s = ite_s.next();
					 //compare and set
					 if(r.rank >= s.rank //rule 1
							 &&r.rank <= s.rank + (sendstoi - sendlist[i][j].size())){ // rule 2
						 sendlistforR.add(s.exp);
				
						 //System.out.println("match (" + r.exp + " " + s.exp+"), total num of sends: " + sendstoi +", and total num of sends for ep " + i + ": " +  sendlist[i][j].size());
					 }
				 }
			 }
			 //add the list with r to the match table
			 if(!sendlistforR.isEmpty())
				 match_table.put(r.exp, sendlistforR);
		 }
	 }
}

	
public class recv{
	public String exp;
	public int rank;
	public String event;
	public recv(String ex, int r, String e){
		exp = ex;
		rank = r;
		event = e;
	}
} 

public class send{
	public String exp;
	public int rank;
	public send(String e, int r){
		exp = e;
		rank = r;
	}
}
	
}
