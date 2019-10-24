package kn.uni.sen.joblibrary.tartar.web;

import java.util.concurrent.TimeUnit;

import org.springframework.boot.SpringApplication;
import org.springframework.http.CacheControl;
import org.springframework.web.servlet.config.annotation.ResourceHandlerRegistry;
import org.springframework.web.servlet.config.annotation.WebMvcConfigurer;

public class TarTarWeb implements WebMvcConfigurer
{
	@Override
	public void addResourceHandlers(ResourceHandlerRegistry registry)
	{
		registry.addResourceHandler("/test/**").addResourceLocations("file:test")
				.setCacheControl(CacheControl.maxAge(2, TimeUnit.HOURS).cachePublic());
		// System.out.println(registry.toString());
	}

	public static void main(String[] args)
	{
		SpringApplication.run(TarTarMain.class, args);
	}

}
