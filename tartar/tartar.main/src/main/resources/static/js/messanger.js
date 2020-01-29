var myVar = setInterval(fire_ajax_submit, 1000);

//$(document).ajaxSend(function(e, xhr, options) {
 //   xhr.setRequestHeader(header, token);
//});

function fire_ajax_submit() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	console.log(csrfToken);
	console.log(sessionID);
	console.log(csrfHeader);
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "/log/msg?",
		data : JSON.stringify(sessionID),
		dataType : 'json',
		cache : false,
		timeout : 600000,
		  beforeSend: function (xhr)
                                 {
                                   xhr.setRequestHeader(csrfHeader, csrfToken);
                                 },
		success : function(data) {
			//var jsonData = JSON.parse(data);
			var msg = data["msg"];
			if(msg)
			{
				var para = document.createElement("div");
				$(para).html(msg);
				document.getElementById("feedback").appendChild(para);
			}
			var logList = data["logList"];
			for (var i = 0; i < logList.length; i++) {
				var para = document.createElement("div");
				$(para).html(logList[i]);
				document.getElementById("feedback").appendChild(para);
			}
			var json = "<pre>"
					+ JSON.stringify(logList, null, 4) + "</pre>";
			//$('#feedback').html(json);
			//console.log("SUCCESS : ", data);
		},
		error : function(e) {
			var json = "<h4>Ajax Error</h4><pre>" + e.responseText
					+ "</pre>";
			$('#feedback2').html(json);
			console.log("ERROR : ", e);
		}
	});
}
