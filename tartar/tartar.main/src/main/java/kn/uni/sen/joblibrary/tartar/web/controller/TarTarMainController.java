package kn.uni.sen.joblibrary.tartar.web.controller;

import java.util.ArrayList;
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
import kn.uni.sen.joblibrary.tartar.web.model.JobRunWeb_TarTar;
import kn.uni.sen.joblibrary.tartar.web.model.JobServerWeb_TarTar;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.core.model.JobRun;

@Controller
@EnableScheduling
public class TarTarMainController
{
	JobServerWeb_TarTar server = new JobServerWeb_TarTar();
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

	JobRunWeb_TarTar getCreateRun(Integer runID, Model model)
	{
		JobRun run = server.createRun(runID);
		model.addAttribute("runID", run.getRunID());
		if (run instanceof JobRunWeb_TarTar)
			return (JobRunWeb_TarTar) run;
		return null;
	}

	JobRunWeb_TarTar getRun(Integer runID)
	{
		JobRun run = server.getRun(runID);
		if (run instanceof JobRunWeb_TarTar)
			return (JobRunWeb_TarTar) run;
		return null;
	}

	/*
	 * @Autowired private SimpMessagingTemplate msgTemplate;
	 */
	@PostMapping("/log/msg")
	public ResponseEntity<?> getSearchResultViaAjax(@Valid @RequestBody Integer runID, Errors errors)
	{
		AjaxResponseBody result = new AjaxResponseBody();
		// If error, just return a 400 bad request, along with the error message
		if (errors.hasErrors())
		{
			result.setMsg(
					errors.getAllErrors().stream().map(x -> x.getDefaultMessage()).collect(Collectors.joining(",")));
			return ResponseEntity.badRequest().body(result);
		}
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
		{
			result.setMsg("Session not found!");
		} else
		{
			// result.setMsg("success");
			while (true)
			{
				JobEvent ev = run.getNextEvent();
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
	public String uploadUppaalFile(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		JobRunWeb_TarTar run = getCreateRun(runID, model);
		if (run == null)
			return "error";
		if (run.hasStarted())
			return "redirect:/results?runID=" + runID;
		run.setAnalysisType(AnalysisTarTarType.ANALYSIS_REPAIR);

		UploadForm form = new UploadForm();
		model.addAttribute("UploadForm", form);
		List<String> fileNames = LibraryTarTar_Console.getModelRepairList();
		form.setFileNameList(fileNames);
		model.addAttribute("fileList", fileNames);
		return "uploadXMIFile";
	}

	@RequestMapping(value = "/facicon.png", method = RequestMethod.GET)
	public String loadIcon(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		return "favicon.png";
	}

	@RequestMapping(value = "/uploadXMIFileSeed", method = RequestMethod.GET)
	public String uploadUppaalFileSeed(@RequestParam(name = "runID", required = false) Integer runID,
			Model model)
	{
		JobRunWeb_TarTar run = getCreateRun(runID, model);
		if (run == null)
			return "error";
		if (run.hasStarted())
			return "redirect:/results?runID=" + runID;
		run.setAnalysisType(AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT);

		UploadForm form = new UploadForm();
		model.addAttribute("UploadForm", form);
		List<String> fileNames = LibraryTarTar_Console.getModelExperimentList();
		form.setFileNameList(fileNames);
		model.addAttribute("fileList", fileNames);
		return "uploadXMIFile";
	}

	@RequestMapping(value = "/uploadXMIFile", method = RequestMethod.POST)
	public String uploadXMIFilePOST(HttpServletRequest request,
			@RequestParam(name = "runID", required = true) Integer runID,
			@ModelAttribute("UploadForm") UploadForm form, Model model)
	{
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
			return "redirect:/index";

		// session.addDescription(form.getDescription());
		if (!!!run.doUpload(request, form))
		{
			return "redirect:/uploadXMIFile?runID=" + runID;
		}
		run.parseModel();
		return "redirect:/parameterRepair?runID=" + runID;
	}

	@RequestMapping(value = "/uploadXMIFileSeed", method = RequestMethod.POST)
	public String uploadXMIFilePOSTSeed(HttpServletRequest request,
			@RequestParam(name = "runID", required = true) Integer runID,
			@ModelAttribute("UploadForm") UploadForm form, Model model)
	{
		return uploadXMIFilePOST(request, runID, form, model);
	}

	@RequestMapping(value = "/parameterRepair", method = RequestMethod.GET)
	public String setOptionsHandler(@RequestParam(name = "runID", required = true) Integer runID, Model model)
	{
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
			return "redirect:/index";

		String[] strArray = run.getPropertyList();
		String[] optionArray = run.getOptionList();

		model.addAttribute("myOptionsForm", new OptionsForm());
		model.addAttribute("propertyList", strArray);
		model.addAttribute("optionList", optionArray);
		model.addAttribute("timeZ3", "120");

		return "parameterRepair";
	}

	@RequestMapping(value = "/parameterRepair", method = RequestMethod.POST)
	public String setOptionsHandlerrPOST(HttpServletRequest request,
			@RequestParam(name = "runID", required = true) Integer runID, Model model, //
			@ModelAttribute("myOptionsForm") OptionsForm form)
	{
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
			return "redirect:/index";
		run.setOptions(form);
		run.verifyModel();

		setLastResult(runID);
		if (run.getAnalysisType() == AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT)
			return "redirect:/resultSeed?runID=" + runID;
		else
			return "redirect:/resultRepair?runID=" + runID;
	}

	private void setLastResult(Integer runID)
	{
		if (LastResult < runID)
			LastResult = runID;
	}

	@RequestMapping(value = "/resultRepair", method = RequestMethod.GET)
	public String showResultRepair(@RequestParam(name = "runID", required = true) Integer runID, Model model)
	{
		JobRunWeb_TarTar run = getRun(runID);
		model.addAttribute("runID", runID);
		if (run == null)
			return "redirect:/index";
		return "resultRepair";
	}

	@RequestMapping(value = "/resultSeed", method = RequestMethod.GET)
	public String showResultSeed(@RequestParam(name = "runID", required = true) Integer runID, Model model)
	{
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
			return "redirect:/index";
		model.addAttribute("runID", run.getRunID());
		return "resultSeed";
	}

	@RequestMapping(value = "/results", method = RequestMethod.GET)
	public String resultsHandler(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		JobRunWeb_TarTar run = getRun(runID);
		if (run == null)
		{
			runID = LastResult;
			run = getRun(runID);
			if (run == null)
				return "index";
		}
		if (run.getAnalysisType() == AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT)
			return "redirect:/resultSeed?runID=" + runID;
		else
			return "redirect:/resultRepair?runID=" + runID;
	}

	@RequestMapping(value = "/analysisRunning", method = RequestMethod.GET)
	public String runningHandler(Model model)
	{
		List<JobData> list = new ArrayList<>();
		for (int i = 1; i < server.getMaxRunID(); i++)
			if (getRun(i) != null)
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
