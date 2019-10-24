package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

public class ModelTransition
{
	int modelID;
	String from;
	String to;
	ConstraintModel guard;
	ConstraintModel assignment;
	ConstraintModel synchron;

	public ModelTransition()
	{
	}

	public void setGuard(ConstraintModel con)
	{
		this.guard = con;
	}

	public ConstraintModel getGuard()
	{
		return this.guard;
	}

	public void setAssignment(ConstraintModel con)
	{
		assignment = con;
	}

	public ConstraintModel getAssignment()
	{
		return assignment;
	}

	public void setSynchronisation(ConstraintModel con)
	{
		synchron = con;
	}

	public ConstraintModel getSynchronisation()
	{
		return synchron;
	}

	public String getFrom()
	{
		return from;
	}

	public void setFrom(String from)
	{
		this.from = from;
	}

	public String getTo()
	{
		return to;
	}

	public void setTo(String to)
	{
		this.to = to;
	}

	public void setIDModel(int id)
	{
		modelID = id;
	}

	public int getIDModel()
	{
		return modelID;
	}

	public void addLabel(String kind, String label)
	{
		ConstraintModel con = new ConstraintModel(modelID, label);

		if (kind.compareTo("guard") == 0)
			setGuard(con);
		else if (kind.compareTo("assignment") == 0)
			setAssignment(con);
		else if (kind.compareTo("synchronisation") == 0)
			setSynchronisation(con);
	}
}
