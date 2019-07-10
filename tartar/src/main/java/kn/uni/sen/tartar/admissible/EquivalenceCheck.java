package kn.uni.sen.tartar.admissible;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import kn.uni.sen.tartar.Diagnostic;
import kn.uni.sen.tartar.uppaal2smt2.ParseUPPAAL;
import kn.uni.sen.tartar.util.Helper;
import kn.uni.sen.tartar.util.ResourceFile;
import kn.uni.sen.tartar.util.ResourceFolder;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.Automata;
import net.automatalib.util.automata.fsa.NFAs;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

/**
 * Checks if two TA are untimed equivalent
 * 
 * @author Martin Koelbl
 */
public class EquivalenceCheck
{
	boolean verbose = false;

	String folderCur = null;
	String folderCurTest = null;
	String folderOpaal = "./opaal";
	List<String> counterList = null;

	static public Diagnostic diagnostic = null;

	{
		String filePath = ResourceFile.getAbsolutePath(".");
		String sign = "/";
		int index = filePath.lastIndexOf(sign);
		File file = null;
		while (index != -1)
		{
			String subPath = filePath.substring(0, index);
			//System.out.println(subPath);
			folderOpaal = subPath + "/opaal";
			file = new File(folderOpaal);
			if (file.exists())
				break;
			index = subPath.lastIndexOf(sign);
		}
		if (!file.exists())
			System.out.println("Error: opaal not found!");

		if (verbose)
			System.out.println("Opaal-Folder: " + folderOpaal);
	}

	public void init(String subFolder)
	{
		try
		{
			folderCur = new java.io.File(".").getCanonicalPath();
			if (folderCur.endsWith("/"))
				folderCur.subSequence(0, folderCur.length() - 1);
			if (subFolder.endsWith("/"))
				subFolder = subFolder.substring(0, subFolder.length() - 1);
			if (!!!subFolder.isEmpty())
				folderCurTest = folderCur + "/" + subFolder;
			else
				folderCurTest = folderCur + "/test";

			ResourceFolder.createFolder(folderCurTest);
			// System.out.println(folderCur);
		} catch (IOException e)
		{
			e.printStackTrace();
		}
	}

	public String getTSfile(String fileTA)
	{
		String fileTS = ResourceFile.getFilenameOnly(fileTA) + "_lts.xml";
		fileTS = folderCurTest + "/" + fileTS;
		return fileTS;
	}

	public String getTAfile(String fileTA)
	{
		String filePath = ResourceFile.getAbsolutePath(fileTA);
		return filePath;
	}

	public static long timeSpace1 = 0;
	public static long timeSpace2 = 0;

	public ResultAdm checkEquivalence(String fileTA1, String fileTA2, String folder)
	{
		if (folderCur == null)
			init(folder);

		// save stm in a file
		// call opaal by python
		String fileTS1 = getTSfile(fileTA1);
		String filePath1 = getTAfile(fileTA1);
		ResourceFile.deleteFile(fileTS1);

		long time = System.currentTimeMillis();
		boolean ret = createTS(filePath1, fileTS1);
		timeSpace1 = System.currentTimeMillis() - time;
		if (!!!ret)
			return null;

		// change folder
		String fileTS2 = getTSfile(fileTA2);
		String filePath2 = getTAfile(fileTA2);
		if (fileTS2.compareTo(fileTS1) == 0)
		{
			fileTS2 = fileTS2.replace(".xml", "2.xml");
		}
		ResourceFile.deleteFile(fileTS2);
		time = System.currentTimeMillis();
		ret = createTS(filePath2, fileTS2);
		timeSpace2 = System.currentTimeMillis() - time;
		if (!!!ret)
			return null;

		ResultAdm res = new ResultAdm();
		res.trace = compareTSs(fileTS1, fileTS2);
		ResourceFile.deleteFile(fileTS1);
		ResourceFile.deleteFile(fileTS2);
		return res;
	}

	boolean createTS(String fileTA, String fileTS)
	{
		// verbose = true;
		// System.out.println("./createTS.sh " + fileTA + " " + fileTS);
		String out = Helper.runCommand("./createTS.sh " + fileTA + " " + fileTS, folderOpaal, verbose);
		if (verbose)
			System.out.println(out);

		File file = new File(fileTS);
		if (file.exists())
			return true;
		System.out.println("Error: State space for admissibility was not created!");
		return false;
	}

	List<String> compareTSs(String fileTS1, String fileTS2)
	{
		AutomatonXMI aut1 = new AutomatonXMI();
		AutomatonXMIHandler handler1 = new AutomatonXMIHandler(aut1);
		ParseUPPAAL.parseFile(fileTS1, handler1);

		AutomatonXMI aut2 = new AutomatonXMI();
		aut2.setEdgeLists(aut1.getEdgeMap(), aut1.getEdgeList());
		AutomatonXMIHandler handler2 = new AutomatonXMIHandler(aut2);
		boolean pRet = ParseUPPAAL.parseFile(fileTS2, handler2);
		if (!!!pRet)
		{
			List<String> l = new ArrayList<>();
			l.add("Error");
			return l;
		}

		List<Integer> list = new ArrayList<>();
		for (Integer v : aut2.getEdgeMap().values())
			list.add(v);
		Alphabet<Integer> alph = Alphabets.fromList(list);

		aut1.createAutomaton(alph);
		aut2.createAutomaton(alph);

		ParseUPPAAL.parseFile(fileTS1, handler1);
		ParseUPPAAL.parseFile(fileTS2, handler2);

		CompactDFA<Integer> dfa1 = NFAs.determinize(aut1.getAutomaton(), alph);
		CompactDFA<Integer> dfa2 = NFAs.determinize(aut2.getAutomaton(), alph);
		boolean ret = Automata.testEquivalence(dfa1, dfa2, alph);

		if (diagnostic != null)
			diagnostic.checkJavaMemory();

		if (ret)
			return null;

		// create counterexample trace
		Word<Integer> trace = Automata.findShortestSeparatingWord(dfa1, dfa2, alph);
		Iterator<Integer> iter = trace.iterator();
		counterList = new ArrayList<>();
		while (iter.hasNext())
		{
			Integer id = iter.next();
			counterList.add(aut2.getEdgeLabel(id));
		}
		return counterList;
	}

	boolean compareTS_LTSmin(String fileTS1, String fileTS2)
	{
		String out = Helper.runCommand("ltsmin-compare --trace " + fileTS1 + " " + fileTS2, folderOpaal, verbose);
		if (verbose)
			System.out.println(out);
		if (Helper.result == 0)
			return true;
		return false;
	}

	// Code of createTS.sh
	// #!/bin/bash
	// #get filename with extension .xml
	// file_in=$1
	// #if no second argument create name of output
	// file_out=$2
	// if [ $# -lt 2 ]
	// then
	// file_out=$file_in.gcf
	// fi
	// file=$(echo "$(basename "${file_out}")" | cut -f 1 -d ".")
	// ./bin/opaal_ltsmin --only-compile $file_in
	// #compile $file.cpp
	// g++ -shared -O0 -fPIC -I/usr/local/uppaal/include -L/usr/local/uppaal/lib
	// -o $file.so $file.cpp -ludbm
	// #run reachability by ltsmin and write TS to $file.gcf
	// opaal2lts-mc --state=table -s=25 --threads=1 --strategy=dfs -u=1 $file.so
	// $file_out

}
