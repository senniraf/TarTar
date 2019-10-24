package kn.uni.sen.joblibrary.tartar.web.controller;

import javax.validation.constraints.NotBlank;

public class User
{
	@NotBlank(message = "username can't empty!")
	String user;

	public String getUser()
	{
		return user;
	}

	public void setUser(String username)
	{
		this.user = username;
	}
}
