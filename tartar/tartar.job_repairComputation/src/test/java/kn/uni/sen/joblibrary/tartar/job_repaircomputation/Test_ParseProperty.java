package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import static org.junit.Assert.assertTrue;
import java.net.URL;
import kn.uni.sen.joblibrary.tartar.modifymodel.ParsePropertyModel;
import kn.uni.sen.joblibrary.tartar.modifymodel.ParsePropertyModel.Property;

public class Test_ParseProperty
{
	// @Test
	public void test()
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL res = classLoader.getResource("0db.xml");
		assertTrue(res != null);

		ParsePropertyModel model = new ParsePropertyModel(res.getFile());
		for (Property form : model.getPropList())
			System.out.println(form.index + ":" + form.form);
	}

	public static void main(String[] args)
	{
		(new Test_ParseProperty()).test();
	}
}
