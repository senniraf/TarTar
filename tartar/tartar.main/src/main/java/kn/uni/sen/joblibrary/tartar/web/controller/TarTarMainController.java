package kn.uni.sen.joblibrary.tartar.web.controller;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

import javax.servlet.http.HttpServletRequest;
import javax.validation.Valid;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.http.ResponseEntity;
import org.springframework.scheduling.annotation.EnableScheduling;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.validation.Errors;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;

import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.joblibrary.tartar.experiment.LibraryTarTar_Console;
import kn.uni.sen.joblibrary.tartar.gui.AnalysisTarTarType;
import kn.uni.sen.joblibrary.tartar.web.form.JobData;
import kn.uni.sen.joblibrary.tartar.web.form.OptionsForm;
import kn.uni.sen.joblibrary.tartar.web.form.UploadForm;
import kn.uni.sen.joblibrary.tartar.web.model.JobWebSession;
import kn.uni.sen.joblibrary.tartar.web.model.JobWebSessionTarTar;
import kn.uni.sen.jobscheduler.common.model.JobEvent;

@Controller
@EnableScheduling
public class TarTarMainController
{
	public static final HashMap<Integer, JobWebSessionTarTar> sessionMap = new HashMap<>();
	private static Integer SessionCounter = 1;
	private static Integer LastResult = 0;

	// Inject via application.properties
	@Value("${welcome.message}")
	private String welcomeMessage;

	@Value("${error.message}")
	private String errorMessage;

	@RequestMapping(value = { "/", "/index" }, method = RequestMethod.GET)
	// short form: @GetMapping

	public String index(Model model)
	{
		model.addAttribute("message", welcomeMessage);

		return "index";
	}

	/*
	 * @Autowired private SimpMessagingTemplate msgTemplate;
	 */
	@PostMapping("/log/msg")
	public ResponseEntity<?> getSearchResultViaAjax(@Valid @RequestBody Integer sessionID, Errors errors)
	{
		AjaxResponseBody result = new AjaxResponseBody();
		// If error, just return a 400 bad request, along with the error message
		if (errors.hasErrors())
		{
			result.setMsg(
					errors.getAllErrors().stream().map(x -> x.getDefaultMessage()).collect(Collectors.joining(",")));
			return ResponseEntity.badRequest().body(result);
		}
		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
		{
			result.setMsg("Session not found!");
		} else
		{
			// result.setMsg("success");
			while (true)
			{
				JobEvent ev = session.getNextEvent();
				if (ev == null)
					break;
				String msg = ev.getText();
				// result.setMsg("");
				result.addLog(msg);
			}
			// result.addLog("Dummy log message");
		}
		return ResponseEntity.ok(result);

	}

	@RequestMapping(value = "/uploadXMIFile", method = RequestMethod.GET)
	public String uploadUppaalFile(@RequestParam(name = "sessionID", required = false) Integer sessionID, Model model)
	{
		JobWebSessionTarTar session = getCreateSession(sessionID, model);
		if (session == null)
			return "error";
		if (session.hasStarted())
			return "redirect:/results?sessionID=" + sessionID;
		session.setAnalysisType(AnalysisTarTarType.ANALYSIS_REPAIR);

		UploadForm form = new UploadForm();
		model.addAttribute("UploadForm", form);
		List<String> fileNames = LibraryTarTar_Console.getModelRepairList();
		form.setFileNameList(fileNames);
		model.addAttribute("fileList", fileNames);
		return "uploadXMIFile";
	}
	
	@RequestMapping(value = "/facicon.png", method = RequestMethod.GET)
	public String loadIcon(@RequestParam(name = "sessionID", required = false) Integer sessionID, Model model)
	{
		return "favicon.png";
	}

	@RequestMapping(value = "/uploadXMIFileSeed", method = RequestMethod.GET)
	public String uploadUppaalFileSeed(@RequestParam(name = "sessionID", required = false) Integer sessionID,
			Model model)
	{
		JobWebSessionTarTar session = getCreateSession(sessionID, model);
		if (session == null)
			return "error";
		if (session.hasStarted())
			return "redirect:/results?sessionID=" + sessionID;
		session.setAnalysisType(AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT);

		UploadForm form = new UploadForm();
		model.addAttribute("UploadForm", form);
		List<String> fileNames = LibraryTarTar_Console.getModelExperimentList();
		form.setFileNameList(fileNames);
		model.addAttribute("fileList", fileNames);
		return "uploadXMIFile";
	}

	JobWebSessionTarTar getCreateSession(Integer sessionID, Model model)
	{
		if ((sessionID == null) || (sessionID > SessionCounter))
		{
			sessionID = SessionCounter;
			SessionCounter++;
			// return "redirect:/uploadXMIFile?sessionID=" + sessionID;
		}

		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
		{
			session = new JobWebSessionTarTar(sessionID);
			sessionMap.put(sessionID, session);
		}
		model.addAttribute("sessionID", session.getId());
		return session;
	}

	@RequestMapping(value = "/uploadXMIFile", method = RequestMethod.POST)
	public String uploadXMIFilePOST(HttpServletRequest request,
			@RequestParam(name = "sessionID", required = true) Integer sessionID,
			@ModelAttribute("UploadForm") UploadForm form, Model model)
	{
		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
			return "redirect:/index";

		// session.addDescription(form.getDescription());
		if (!!!session.doUpload(request, form, session))
		{
			return "redirect:/uploadXMIFile?sessionID=" + sessionID;
		}
		session.parseModel();
		return "redirect:/parameterRepair?sessionID=" + sessionID;
	}

	@RequestMapping(value = "/uploadXMIFileSeed", method = RequestMethod.POST)
	public String uploadXMIFilePOSTSeed(HttpServletRequest request,
			@RequestParam(name = "sessionID", required = true) Integer sessionID,
			@ModelAttribute("UploadForm") UploadForm form, Model model)
	{
		return uploadXMIFilePOST(request, sessionID, form, model);
	}

	@RequestMapping(value = "/parameterRepair", method = RequestMethod.GET)
	public String setOptionsHandler(@RequestParam(name = "sessionID", required = true) Integer sessionID, Model model)
	{
		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
			return "redirect:/index";

		String[] strArray = session.getPropertyList();
		String[] optionArray = session.getOptionList();

		model.addAttribute("myOptionsForm", new OptionsForm());
		model.addAttribute("propertyList", strArray);
		model.addAttribute("optionList", optionArray);
		model.addAttribute("timeZ3", "120");

		return "parameterRepair";
	}

	@RequestMapping(value = "/parameterRepair", method = RequestMethod.POST)
	public String setOptionsHandlerrPOST(HttpServletRequest request,
			@RequestParam(name = "sessionID", required = true) Integer sessionID, Model model, //
			@ModelAttribute("myOptionsForm") OptionsForm form)
	{
		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
			return "redirect:/index";
		session.setOptions(form);
		session.verifyModel();

		setLastResult(sessionID);
		if (session.getAnalysisType() == AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT)
			return "redirect:/resultSeed?sessionID=" + sessionID;
		else
			return "redirect:/resultRepair?sessionID=" + sessionID;
	}

	private void setLastResult(Integer sessionID)
	{
		if (LastResult < sessionID)
			LastResult = sessionID;
	}

	@RequestMapping(value = "/resultRepair", method = RequestMethod.GET)
	public String showResultRepair(@RequestParam(name = "sessionID", required = true) Integer sessionID, Model model)
	{
		JobWebSession session = sessionMap.get(sessionID);
		model.addAttribute("sessionID", sessionID);
		if (session == null)
			return "redirect:/index";
		return "resultRepair";
	}

	@RequestMapping(value = "/resultSeed", method = RequestMethod.GET)
	public String showResultSeed(@RequestParam(name = "sessionID", required = true) Integer sessionID, Model model)
	{
		JobWebSession session = sessionMap.get(sessionID);
		model.addAttribute("sessionID", sessionID);
		if (session == null)
			return "redirect:/index";
		return "resultSeed";
	}

	@RequestMapping(value = "/results", method = RequestMethod.GET)
	public String resultsHandler(@RequestParam(name = "sessionID", required = false) Integer sessionID, Model model)
	{
		JobWebSessionTarTar session = sessionMap.get(sessionID);
		if (session == null)
		{
			sessionID = LastResult;
			session = sessionMap.get(LastResult);
			if (session == null)
				return "index";
		}
		if (session.getAnalysisType() == AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT)
			return "redirect:/resultSeed?sessionID=" + sessionID;
		else
			return "redirect:/resultRepair?sessionID=" + sessionID;
	}

	@RequestMapping(value = "/analysisRunning", method = RequestMethod.GET)
	public String runningHandler(Model model)
	{
		List<JobData> list = new ArrayList<>();
		for (int i = 1; i < SessionCounter; i++)
			if (sessionMap.get(i) != null)
				list.add(new JobData("" + i, ""));
		model.addAttribute("SessionList", list);
		return "analysisRunning";
	}

	@RequestMapping(value = "/info", method = RequestMethod.GET)
	public String infoHandler(Model model)
	{
		List<JobData> list = new ArrayList<>();
		list.add(new JobData("TarTar Web", TarTarConfiguration.getVersion()));
		model.addAttribute("JobList", list);
		return "info";
	}
}
