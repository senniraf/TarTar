package kn.uni.sen.joblibrary.tartar.web.controller;

import java.util.ArrayList;
import java.util.List;

public class AjaxResponseBody
{
	String msg = "";
	List<String> logList = new ArrayList<>();

	// getters and setters
	public void setLogList(List<String> list)
	{
		logList = list;
	}

	public void addLog(String log)
	{
		logList.add(log);
	}

	public List<String> getLogList()
	{
		return logList;
	}

	public String getMsg()
	{
		return msg;
	}

	public void setMsg(String msg)
	{
		this.msg = msg;
	}
}
