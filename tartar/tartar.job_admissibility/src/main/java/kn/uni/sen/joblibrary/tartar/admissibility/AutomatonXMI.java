package kn.uni.sen.joblibrary.tartar.admissibility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import net.automatalib.automata.fsa.impl.FastNFA;
import net.automatalib.automata.fsa.impl.FastNFAState;
import net.automatalib.words.Alphabet;

public class AutomatonXMI
{
	List<String> edgeList = new ArrayList<>();
	List<String> stateList = new ArrayList<>();
	HashMap<String, Integer> edgeMap = new HashMap<>();
	Alphabet<Integer> alpha = null;

	HashMap<String, FastNFAState> stateMap = new HashMap<>();

	FastNFA<Integer> automaton = null;
	int count = 1;

	public void addState(String text, boolean initial)
	{
		createState(text, initial);
	}

	public void createAutomaton(Alphabet<Integer> alpha)
	{
		this.alpha = alpha;
		automaton = new FastNFA<>(this.alpha);
	}

	protected FastNFAState createState(String text, boolean initial)
	{
		if (automaton == null)
			return null;
		for (String s : stateList)
			if (s.compareTo(text) == 0)
				return stateMap.get(s);
		stateList.add(text);
		FastNFAState state;
		if (initial)
			state = automaton.addInitialState();
		else
			state = automaton.addState();
		state.setAccepting(true);
		stateMap.put(text, state);
		return state;
	}

	String getUniqueEdgeString(String text)
	{
		for (String s : edgeList)
			if (s.compareTo(text) == 0)
				return s;
		edgeList.add(text);
		// System.out.println(text);
		return text;
	}

	public void addEdge(String from, String to, String label)
	{
		label = getUniqueEdgeString(label);
		Integer val = edgeMap.get(label);
		if (automaton == null)
		{
			if (val == null)
			{
				val = count++;
				edgeMap.put(label, val);
			}
			return;
		}
		if (val == null)
		{
			System.out.println("Error: label " + label + " is missing.");
			return;
		}

		FastNFAState stateFrom = createState(from, false);
		FastNFAState stateTo = createState(to, false);
		automaton.addTransition(stateFrom, val, stateTo);
	}

	public FastNFA<Integer> getAutomaton()
	{
		return automaton;
	}

	public HashMap<String, Integer> getEdgeMap()
	{
		return edgeMap;
	}

	public Alphabet<Integer> getAlphabet()
	{
		return alpha;
	}

	public void setEdgeLists(HashMap<String, Integer> edgeMap, List<String> edgeList)
	{
		this.edgeMap = edgeMap;
		this.edgeList = edgeList;
		count += edgeMap.size();
	}

	public List<String> getEdgeList()
	{
		return edgeList;
	}

	public String getEdgeLabel(Integer id)
	{
		// todo: very computation intensive
		for (String str : edgeList)
			if (edgeMap.get(str) == id)
				return str;
		return "Error:Missing!";
	}
}
