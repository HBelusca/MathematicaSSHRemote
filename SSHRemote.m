(* ::Package:: *)

(* ::Title:: *)
(*SSHRemote package v2.0a*)


(* ::Subtitle:: *)
(*A Mathematica package that implements remote kernels launch through tunnelled SSH connections.*)
(*It interfaces with the standard Mathematica LaunchKernels[RemoteMachine[...]] functionality by overloading the SubKernels`RemoteKernels package.*)


(* ::Subsubtitle:: *)
(*Copyright 2018 Herm\[EGrave]s B\[EAcute]lusca-Ma\[IDoubleDot]to, under the GPL-2.0+ (https://spdx.org/licenses/GPL-2.0+) license.*)


(* ::Text:: *)
(*This package attempts at solving the problem described in https://mathematica.stackexchange.com/questions/65953/remote-kernel-through-ssh ,*)
(*where the following constraints apply:*)
(*- both the local and the remote computer are behind a firewall,*)
(*- the SSH connection requires authentication via manual password entering, without using SSH keys,*)
(*- the code should be written in Wolfram Language.*)
(**)
(*The key point is to create an SSH tunnel with remote port forwardings.*)
(**)
(*This code is inspired from two sources:*)
(*- from the "MathematicaSSHKernels" package, at: https://github.com/Riebart/MathematicaSSHKernels*)
(*  (see also the associated discussion at: http://community.wolfram.com/groups/-/m/t/1394764),*)
(*- and from the "Tunnel" package by Sascha Kratky, at: https://github.com/sakra/Tunnel (the historical version can be found at: http://library.wolfram.com/infocenter/Conferences/7250/)*)
(*  that was mentioned in the following discussion: https://mathematica.stackexchange.com/questions/28274/remote-kernel-error-mleconnect .*)


BeginPackage["SSHRemote`", {(*"SubKernels`LinkKernels`",*)"SubKernels`RemoteKernels`"}]


Unprotect[LaunchRemote, RemoteMachine];


(* ::Subsection:: *)
(*Backwards-compatibility*)


If[$VersionNumber<7,
  System`FileNameJoin[names_List]:=ToFileName[Sequence @@ If[names =!= {}, {names[[;; -2]], names[[-1]]}, {names}]];
];
If[$VersionNumber<10,
  System`BooleanQ[expr_]:=MatchQ[expr,True|False];
];
If[$VersionNumber<10.2,
  System`FailureQ[expr_]:=MatchQ[expr,_Failure|$Failed|$Aborted];
];
(* Basic version of StringRiffle[] *)
If[$VersionNumber<10.1,
  StringRiffle[list_List,sep_String]:=StringJoin@Riffle[If[!StringQ[#],ToString[#],#]&/@list,sep];
  StringRiffle[list_List]:=StringRiffle[list," "];
]


(* ::Subsection:: *)
(*Patching FilterRules[]*)


(* ::Text:: *)
(*FilterRules[] is patched because it does not behave well when the pattern is Except[c,p].*)


Begin["`Private`"]

getRuleLHS[rule:(_Rule|_RuleDelayed)]:=First[rule];
getRuleLHS[expr_String]:=Symbol[expr];
getRuleLHS[expr_]:=expr;

(*
Unprotect[FilterRules];
FilterRules[rule:(_Rule|_RuleDelayed), patt_] := FilterRules[{rule},patt];
FilterRules[rules:{(_Rule|_RuleDelayed)..}, Except[cPatt_List,patt_List]] := Select[rules, MatchQ[getRuleLHS@#, Except[Alternatives@@getRuleLHS/@cPatt,Alternatives@@getRuleLHS/@patt]]&];
FilterRules[rules:{(_Rule|_RuleDelayed)..}, Except[cPatt_List,patt_]] := Select[rules, MatchQ[getRuleLHS@#, Except[Alternatives@@getRuleLHS/@cPatt,getRuleLHS@patt]]&];
FilterRules[rules:{(_Rule|_RuleDelayed)..}, Except[cPatt_,patt_List]] := Select[rules, MatchQ[getRuleLHS@#, Except[getRuleLHS@cPatt,Alternatives@@getRuleLHS/@patt]]&];
FilterRules[rules:{(_Rule|_RuleDelayed)..}, Except[cPatt_,patt_]] := Select[rules, MatchQ[getRuleLHS@#, Except[getRuleLHS@cPatt,getRuleLHS@patt]]&];
Protect[FilterRules];
*)
End[]


(* ::Subsection::Closed:: *)
(*Error handling, error messages*)


General::npos=General::estep; (* "Value of option `1` -> `2` is not a positive integer." *)


Begin["`Private`"];

ValidateCondition::usage=
"ValidateCondition[condition_, errorMsgStr_String, opts___, failAction_:Abort[]]
ValidateCondition[condition_, errorMsgName_MessageName:(General::asrtf), opts___, failAction_:Abort[]]

Verifies that the specified condition is True, and if not, displays an error message and aborts the computation or perform a user-specific failure action.
The error message is specified via either a message name or a control string.";

ValidateOption::usage=
"ValidateOption[optValue_, optName_Symbol, optPossibleValues_, errorMsgStr_String, failAction_:Abort[]]
ValidateOption[optValue_, optName_Symbol, optPossibleValues_, errorMsgName_MessageName:(General::optvg), failAction_:Abort[]]

Verifies that the provided value 'optValue' matches one of the possible values 'optPossibleValues' for the option 'optName', and if not, displays an error message and aborts the computation or perform a user-specific failure action.
The error message is specified via either a message name or a control string.";

SetAttributes[ValidateCondition, HoldAll]; (* 'HoldAll' attribute must be acquired first for the 'failAction' specification to be correctly set *)

ValidateCondition[condition_, errorMsgStr_String, opts___, failAction_:Abort[]] :=
  If[!condition, Print@StringForm[errorMsgStr, If[opts===Null, condition, Sequence@@{opts}]]; failAction];

ValidateCondition[condition_, errorMsgName_MessageName:(General::asrtf), opts___, failAction_:Abort[]] :=
  If[!condition, Message[errorMsgName, If[opts===Null, condition, Sequence@@{opts}]]; failAction];

SetAttributes[ValidateCondition, Protected];

SetAttributes[ValidateOption, HoldAll]; (* 'HoldAll' attribute must be acquired first for the 'failAction' specification to be correctly set *)

ValidateOption[optValue_, optName_Symbol, optPossibleValues_, errorMsgStr_String, failAction_:Abort[]] :=
  ValidateCondition[MatchQ[optValue, optPossibleValues], errorMsgStr, optName, optValue, optPossibleValues, failAction];

ValidateOption[optValue_, optName_Symbol, optPossibleValues_, errorMsgName_MessageName:(General::optvg), failAction_:Abort[]] :=
  ValidateCondition[MatchQ[optValue, optPossibleValues], errorMsgName, InputForm@optName, InputForm@optValue, InputForm@optPossibleValues, failAction];

SetAttributes[ValidateOption, Protected];

End[]; (* "`Private`" *)


(* ::Subsection:: *)
(*Symbols descriptions*)


SSHRemote`SSHRemote::usage="SSHRemote is a symbol that is used in the overloaded definitions of RemoteMachine[] and LaunchRemote[] to specify that the functionalities of the SSHRemote` package have to be used instead.";


Off[General::shdw]; (* Switch off shadowing warnings for Verbose, Asynchronous and OperatingSystem *)


SSHRemote`SshLaunchRemote::usage=
"SshLaunchRemote[host_String, n:(_Integer?NonNegative):1, OptionsPattern[]] -- Uses $RemoteUserName and $RemoteCommand as default values.
SshLaunchRemote[host_String, cmdTemplate_String, n:(_Integer?NonNegative):1, OptionsPattern[]] -- Uses $RemoteUserName as default value.
SshLaunchRemote[host_String, username_String, cmdTemplate_String, n:(_Integer?NonNegative):1, OptionsPattern[]]

Starts n remote kernels via an SSH connection to the specified host and user. The specific remote kernel command is specified via the cmdTemplate parameter; see ?$RemoteCommand for the specific syntax.

The valid options are:
- Multiplexing\[Rule]True|False: Whether or not a multiplexed SSH connection is used when starting n kernels. When a multiplexed SSH connection is used, the login is requested only once, and the remote kernels all share the same SSH connection. The default value is False.
- MultiplexingCommands\[Rule]{startCmd_String, ctlCmd_String}: Custom commands to manipulate the multiplexed SSH connection.
- Verbose\[Rule]True|False: Whether or not diagnostic messages are displayed during connection. The default value is False.
";
SSHRemote`Multiplexing::usage="Multiplexing is an option for SshLaunchRemote[]. Multiplexing\[Rule]True|False: Whether or not a multiplexed SSH connection is used when starting n kernels. When a multiplexed SSH connection is used, the login is requested only once, and the remote kernels all share the same SSH connection. The default value is False.";
SSHRemote`MultiplexingCommands::usage="MultiplexingCommands is an option for SshLaunchRemote[]. MultiplexingCommands\[Rule]{startCmd_String, ctlCmd_String}: Custom commands to manipulate the multiplexed SSH connection.";
SSHRemote`Verbose::usage="Verbose is an option for SshLaunchRemote[]. Verbose\[Rule]True|False: Whether or not diagnostic messages are displayed during connection. The default value is False.";


SSHRemote`AdjustCommandLine::usage=
"AdjustCommandLine[cmdLine_String, OptionsPattern[]]
Adjusts the specified command line for a specific operating system.

The valid options are:
- Asynchronous\[Rule]True|False: Whether or not support for asynchronous command should be added. The default value is False.
- OperatingSystem\[Rule]\"Windows\"|\"WSL\"|\"WSLNew\"|\"Unix\"|\"MacOSX\": The choice of operating system: \"Windows\", \"Unix\", or \"MacOSX\" for one of these operating systems.
  The options \"WSL\" or \"WSLNew\" correspond to the 'Windows Subsystem for Linux', and are only valid on Windows 10 x64 version 1607 and above.
  See https://docs.microsoft.com/en-us/windows/wsl/about , https://docs.microsoft.com/en-us/windows/wsl/faq , and https://docs.microsoft.com/en-us/windows/wsl/install-win10 for more details.
  The default value is given by the value of $OperatingSystem.
";
SSHRemote`Asynchronous::usage="Asynchronous is an option for AdjustCommandLine[]. Asynchronous\[Rule]True|False: Whether or not support for asynchronous command should be added. The default value is False.";
SSHRemote`OperatingSystem::usage="OperatingSystem is an option for AdjustCommandLine[]. OperatingSystem\[Rule]\"Windows\"|\"WSL\"|\"WSLNew\"|\"Unix\"|\"MacOSX\": The choice of operating system: \"Windows\", \"Unix\", or \"MacOSX\" for one of these operating systems.
The options \"WSL\" or \"WSLNew\" correspond to the 'Windows Subsystem for Linux', and are only valid on Windows 10 x64 version 1607 and above.
See https://docs.microsoft.com/en-us/windows/wsl/about , https://docs.microsoft.com/en-us/windows/wsl/faq , and https://docs.microsoft.com/en-us/windows/wsl/install-win10 for more details.
The default value is given by the value of $OperatingSystem.";


On[General::shdw]; (* Restore shadowing warnings *)


SshRemoteMachine::usage="SshRemoteMachine[host, username, (template), (n), opts...] is a shortcut notation for RemoteMachine[host, SSHRemote, username, (template), (n), opts...].";


SshLaunchKernels::usage="SshLaunchKernels[host, username, (template), (n), opts...] is a shortcut notation for LaunchKernels[SshRemoteMachine[host, username, (template), (n), opts...]].";


RemoteMachine::usage = StringJoin[RemoteMachine::usage,"\n",
"RemoteMachine[host, username, (template), (n), opts...] also supports for an explicit user-name specification, whose default value is $RemoteUserName.
RemoteMachine[host, SSHRemote, username, (template), (n), opts...] specifies that the functionalities of the SSHRemote` package have to be used."
];


LaunchRemote::usage = StringJoin[LaunchRemote::usage,"\n",
"LaunchRemote[host, username, template, opts..] also supports for an explicit user-name specification, whose default value is $RemoteUserName.
LaunchRemote[host, SSHRemote, username, template, opts..] specifies that the functionalities of the SSHRemote` package have to be used."
];


SSHRemote`$SshSocketsPath::usage="$SshSocketsPath defines the platform-and-user-specific SSH sockets path.";
SSHRemote`$SshCmd::usage="$SshCmd defines the standard SSH connection command that is used for starting remote kernels. See also $mathCmd.";
SSHRemote`$SshCmdMultiplex::usage="$SshCmdMultiplex defines the SSH connection command that is used for starting remote kernels when SSH multiplexed connections are used.";
SSHRemote`$SshMultiplexStart::usage="$SshMultiplexStart defines the SSH command that is used to start a new SSH multiplexed connection.";
SSHRemote`$SshMultiplexCtlCmd::usage="$SshMultiplexCtlCmd defines the SSH command that is used to control existing SSH multiplexed connections.";


SSHRemote`$mathCmd::usage="$mathCmd is the remote Mathematica kernel launch command. See also $mathkernel.";


(* ::Subsection:: *)
(*Constants*)


(* ::Text:: *)
(*SSH sockets path (platform-specific).*)


$SshSocketsPath="~/.ssh/sockets/";


(* ::Text:: *)
(*SSH commands. See https://linux.die.net/man/1/ssh for more details.*)
(*The options (not all are recognized by SSH clients) are:*)
(*-f start as background process.*)
(*-C enable compression.*)
(*-v verbose mode.*)
(*-x disable X11 forwarding.*)
(*-n prevent reading from stdin.*)
(*-T disable pseudo-tty allocation.*)
(*-A enable SSH agent forwarding.*)


$SshCmd="ssh `3`@`1` -C "<>(*"-v "<>*)"-x -n -T -A `ports`"(*<>" -o CheckHostIP=no -o StrictHostKeyChecking=no -o ControlMaster=no"*);

(* SSH Multiplexed connections support -- See https://en.wikibooks.org/wiki/OpenSSH/Cookbook/Multiplexing for more details *)
$SshCmdMultiplex="ssh `3`@`1` -f -C "<>(*"-v "<>*)"-x -n -T -A -o ControlMaster=no -o ControlPath="<>$SshSocketsPath<>"ssh-%r@%h:%p";

(* Start the multiplexed connection *)
$SshMultiplexStart="ssh `3`@`1` -fN -C "<>(*"-v "<>*)"-x -n -T -A -o ControlMaster=yes -o ControlPath="<>$SshSocketsPath<>"ssh-%r@%h:%p";

(* Multiplex control commands -- For stopping the multiplexed connection we use ctlcmd \[Equal] stop ; alternatively one can use "-O exit" to kill all the connections. *)
$SshMultiplexCtlCmd="ssh `3`@`1` -O `ctlcmd` `params` -o ControlPath="<>$SshSocketsPath<>"ssh-%r@%h:%p";


(* ::Text:: *)
(*Remote Mathematica kernel launch command (see also $mathkernel).*)


$mathCmd="\"MathKernel -wstp "<>(*"-mathlink "<>*)"-lmverbose -LinkMode Connect `4` -LinkName `2`"<>(*" -LinkHost `ipaddress`"<>*)" -subkernel" (*  -noinit -remotelaunch -nopaclet  2>&1 & *)(*<>" >& /dev/null &"*)(*<>"&; exit"*)<>"\"";


(* ::Subsection:: *)
(*Implementation*)


(* Protected/locked symbol to be used to distinguish the overloaded definitions of RemoteMachine[] and LaunchRemote[] and their original definitions. *)
SetAttributes[SSHRemote,{Protected,Locked}];


Begin["`Private`"]


If[$VersionNumber<10.1,

General::somefail = "`2` of `1` kernels failed to launch.";

SubKernels`Protected`deleteFailed[l_List, msghead_:Null] :=
With[{nl = DeleteCases[l, $Failed]},
	If[Length[nl]<Length[l] && msghead=!=Null, Message[msghead::somefail, Length[l], Length[l]-Length[nl]]];
	nl
];

SubKernels`Protected`firstOrFailed[l_List] := First[l, $Failed];

];


(* description language methods *)
RemoteMachine /: SubKernels`KernelCount[RemoteMachine[host_, username_String:"", cmd_String:"", n_Integer:1, opts:OptionsPattern[]]] := n;
RemoteMachine /: SubKernels`KernelCount[RemoteMachine[host_, SSHRemote, username_String:"", cmd_String:"", n_Integer:1, opts:OptionsPattern[]]] := n;

(* format of description items *)
Format[RemoteMachine[host_, username_String:"", cmd_String:"", n_Integer:1, OptionsPattern[]]/;n==1] :=
	StringForm["\[LeftSkeleton]a kernel on `1`\[RightSkeleton]", host];
Format[RemoteMachine[host_, username_String:"", cmd_String:"", n_Integer:1, OptionsPattern[]]/;n>1] :=
	StringForm["\[LeftSkeleton]`1` kernels on `2`\[RightSkeleton]", n, host];
Format[RemoteMachine[host_, SSHRemote, username_String:"", cmd_String:"", n_Integer:1, OptionsPattern[]]/;n==1] :=
	StringForm["\[LeftSkeleton]a kernel on `1`\[RightSkeleton]", host];
Format[RemoteMachine[host_, SSHRemote, username_String:"", cmd_String:"", n_Integer:1, OptionsPattern[]]/;n>1] :=
	StringForm["\[LeftSkeleton]`1` kernels on `2`\[RightSkeleton]", n, host];


(* Shortcut helpers *)
SshRemoteMachine[host_, args___]:=RemoteMachine[host, SSHRemote, args];
SshLaunchKernels[args___]:=LaunchKernels[SshRemoteMachine[args]];


(* ::Text:: *)
(*Standard paths to Java and MathSSH.*)


$JavaCommand = FileNameJoin[{$InstallationDirectory,"SystemFiles","Java",$SystemID,"bin","java"}];
$WolframSSH = $MathSSH = FileNameJoin[{$InstallationDirectory,"SystemFiles","Java","WolframSSH.jar"}];


cmdLineRun[cmdTemplate_String, verbose_?BooleanQ, msgTemplate_String:"", strRepRules:{(_String->_) ...}, strFormExprs_List]:=
Module[{cmdLine},
  (* Build the full command line *)
  cmdLine=StringReplace[cmdTemplate, {"`java`"->$JavaCommand, "`mathssh`"->$MathSSH, "`wolframssh`"->$WolframSSH, Sequence@@strRepRules}];
  cmdLine=StringForm[cmdLine, Sequence@@strFormExprs];
  If[verbose, Print@StringForm[msgTemplate,cmdLine]];

  (* Start it *)
  {Run[cmdLine],cmdLine}
];


(* ::Text:: *)
(*See https://mathematica.stackexchange.com/a/98478 for more information about SyntaxInformation[] and for "OptionNames".*)
(*See https://mathematica.stackexchange.com/questions/18674/evaluation-of-optionvalue for more information about evaluation of OptionValue[].*)


optionNames=ToString/@Apply[Join,Options/@{##}][[All,1]]&;


Options[SshLaunchRemote]=Join[Options[LaunchRemote], {SSHRemote`Multiplexing->False, SSHRemote`MultiplexingCommands->{(* Start *)"",(* Control commands *)""}, Verbose->False}];

SyntaxInformation[SshLaunchRemote]={"ArgumentsPattern"->{_,_,__,OptionsPattern[]}, "OptionNames"->optionNames[SshLaunchRemote]};

SshLaunchRemote[host_String, n:(_Integer?NonNegative):1, opts:OptionsPattern[]]:=
  SshLaunchRemote[host, $RemoteUserName, $RemoteCommand, n, opts];

SshLaunchRemote[host_String, cmdTemplate_String, n:(_Integer?NonNegative):1, opts:OptionsPattern[]]:=
  SshLaunchRemote[host, $RemoteUserName, cmdTemplate, n, opts];

SshLaunchRemote[host_String, username_String, cmdTemplate_String, n:(_Integer?NonNegative):1, opts:OptionsPattern[]]:=
Module[{multiplex,multiplexCmds,verbose,java,wolframssh,mathssh,links,cmdLine,code},
  {multiplex,multiplexCmds,verbose}=OptionValue@{SSHRemote`Multiplexing,SSHRemote`MultiplexingCommands,Verbose};
  ValidateCondition[BooleanQ[multiplex], General::opttf, MultiplexingCommands, multiplex];
  If[!MatchQ[multiplexCmds,{_String,_String}],Message[General::irule,multiplexCmds];Abort[]];(*General::optrs*)
  ValidateCondition[BooleanQ[verbose], General::opttf, Verbose, verbose];
  ValidateCondition[n>0, "The number of kernels must be a positive integer!"];

  If[multiplex,Print["SSH with Multiplexing"],Print["SSH with NO Multiplexing"]];

  (* Create new connection links *)
  links=Table[LinkCreate[LinkProtocol->"TCPIP"],{n}];
  links=SubKernels`Protected`deleteFailed[links,SshLaunchRemote];

  (* Start SSH multiplexing mode if needed *)
  If[multiplex&&multiplexCmds[[1]]=!="",
    {code,cmdLine}=cmdLineRun[multiplexCmds[[1]], verbose, "SSH multiplexing mode command line: '`1`'", {(*"`ports`"\[Rule]sshPorts*)}, {host,username,username}];
    If[code!=0,Print["Failed to start SSH multiplexing mode on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
  ];

  Module[{link=#,linkPorts,sshPorts,linkName},
    (* Parse the TCPIP link names and extract the link ports *)
    linkPorts=Function[{link},link[[1]]//(Reverse[StringSplit[#,"@"]]&)/@StringSplit[#,","]&]@link;

    (* Set up remote port forwardings for kernel main link. Note that no local port forwardings are required for compute kernels. *)
    sshPorts=StringRiffle@(StringRiffle[Join[{"-R 127.0.0.1",#[[2]]},#],":"]&/@linkPorts);

    (* Build the correct forwarded link name *)
    linkName=StringRiffle[(#<>"@127.0.0.1")&/@linkPorts[[All,2]],","];

    (* Set port forwarding in SSH multiplexing mode if needed *)
    If[multiplex,
      {code,cmdLine}=cmdLineRun[multiplexCmds[[2]], verbose, "SSH multiplexing mode port forwarding command line: '`1`'", {"`ctlcmd`"->"forward","`params`"->sshPorts}, {host,username,username}];
      If[code!=0,Print["Failed to set SSH multiplexing mode port forwarding on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
    ];

    (* Build the full command line and start it *)
    {code,cmdLine}=cmdLineRun[cmdTemplate, verbose, "Full command line: '`1`'", {"`ports`"->If[multiplex,"",sshPorts],"`linkname`"->linkName,"`ipaddress`"->"127.0.0.1"}, {host,linkName,username,"-LinkProtocol TCPIP"}];
    If[code!=0,Print["Failed to start SSH remote kernel on ",host," !"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];LinkClose[link];];
  ]&/@links;

  (* Stop port forwarding in SSH multiplexing mode if needed *)
  If[multiplex,
    {code,cmdLine}=cmdLineRun[multiplexCmds[[2]], verbose, "SSH multiplexing mode port forwarding command line: '`1`'", {"`ctlcmd`"->"stop","`params`"->""}, {host,username,username}];
    If[code!=0,Print["Failed to set SSH multiplexing mode port forwarding on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
  ];

  (* Attempt to connect to the kernels. If it succeeds, we don't need to close the links; they will be automatically closed when the kernels are terminated using CloseKernels[]. *)
  (** Module[{link=#,kernel},kernel=LaunchKernels[link];If[FailureQ[kernel],Print["Failed to start a remote kernel on ",host," !"];LinkClose[link];];kernel]&/@links **)
  initLink[links, host,
    {host,SSHRemote,username,cmdTemplate,
      (* If new kernels need to be restarted/cloned, this should be done using a non-multiplexed SSH connection *)
      (* FilterRules[{opts}, Except[{SSHRemote`Multiplexing,SSHRemote`MultiplexingCommands}, Options[SshLaunchRemote]]] *)
      Select[{opts}, MatchQ[getRuleLHS@#, Except[Alternatives@@getRuleLHS/@{SSHRemote`Multiplexing,SSHRemote`MultiplexingCommands},Alternatives@@getRuleLHS/@Options[SshLaunchRemote]]]&]
    },
    OptionValue[SshLaunchRemote, {opts}, KernelSpeed] ]
];


(* raw constructor; several at once *)
initLink[links_List, host_, args_, sp_] :=
 Module[{kernels},
 	(* each kernel gets its own set of variables for the mutable fields *)
 	kernels = Module[{speed=sp}, remoteKernel[ SubKernels`RemoteKernels`Private`lk[#, host, args, speed] ]]& /@ links;
 	(* local init *)
 	AppendTo[SubKernels`RemoteKernels`Private`$openkernels, kernels];
 	(* base class init *)
 	SubKernels`Protected`kernelInit[kernels]
 ]

(* single one *)
initLink[link_, args__] := SubKernels`Protected`firstOrFailed[ initLink[{link}, args] ]


(* Version of LaunchRemote[] with explicit user name; calls the original LaunchRemote[] back. *)
LaunchRemote[host_String, username_String, cmd_String, opts:OptionsPattern[]] := SubKernels`Protected`firstOrFailed[ LaunchRemote[host, username, cmd, 1, opts] ];
LaunchRemote[host_String, username_String, cmd_String, n_Integer?NonNegative, opts:OptionsPattern[]] := Block[{$RemoteUserName=username}, LaunchRemote[host, cmd, n, opts]];

(* Version of LaunchRemote[] that calls SshLaunchRemote[] *)

LaunchRemote[host_String, SSHRemote, opts:OptionsPattern[]] := LaunchRemote[host, SSHRemote, $RemoteUserName, $RemoteCommand, opts];
LaunchRemote[host_String, SSHRemote, n_Integer?NonNegative, opts:OptionsPattern[]] := LaunchRemote[host, SSHRemote, $RemoteUserName, $RemoteCommand, n, opts];

LaunchRemote[host_String, SSHRemote, cmdTemplate_String, opts:OptionsPattern[]] := LaunchRemote[host, SSHRemote, $RemoteUserName, cmdTemplate, opts];
LaunchRemote[host_String, SSHRemote, cmdTemplate_String, n_Integer?NonNegative, opts:OptionsPattern[]] := LaunchRemote[host, SSHRemote, $RemoteUserName, cmdTemplate, n, opts];

(* default n is 1 *)
LaunchRemote[host_String, SSHRemote, username_String, cmdTemplate_String, opts:OptionsPattern[]] :=
  SubKernels`Protected`firstOrFailed[ LaunchRemote[host, SSHRemote, username, cmdTemplate, 1, opts] ];

(* parallel launching *)
LaunchRemote[host_String, SSHRemote, username_String, cmdTemplate_String, n_Integer?NonNegative, opts:OptionsPattern[]] :=
  SshLaunchRemote[host, username, cmdTemplate, n, opts];


Options[AdjustCommandLine]={SSHRemote`Asynchronous->False, SSHRemote`OperatingSystem->$OperatingSystem};

SyntaxInformation[AdjustCommandLine]={"ArgumentsPattern"->{_,OptionsPattern[]}, "OptionNames"->(*optionNames[AdjustCommandLine]*){"Asynchronous","OperatingSystem"}};

AdjustCommandLine[cmdLine_String, OptionsPattern[]]:=
Module[{async,os},
  {async,os}=OptionValue@{SSHRemote`Asynchronous,SSHRemote`OperatingSystem};
  ValidateCondition[BooleanQ[async], General::opttf, Asynchronous, async];
  ValidateOption[os, OperatingSystem, "Windows"|"WSL"|"WSLNew"|"Unix"|"MacOSX"];

  Switch[os,
    "Windows",
      If[async,"start ",""]<>cmdLine
    ,
    "WSL",
      If[async,"start ",""]<>"bash -c "<>ToString[cmdLine,InputForm]
    ,
    "WSLNew",
      If[async,"start ",""]<>(*"wsl -e "*)"wsl "<>cmdLine
    ,
    _ (* "Unix" | "MacOSX" *),
      cmdLine<>If[async," &",""]
  ]
];


Protect[SshLaunchKernels, SshLaunchRemote, SshRemoteMachine, AdjustCommandLine];


End[]


Protect[LaunchRemote, RemoteMachine];


EndPackage[]
