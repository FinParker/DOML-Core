# DOML-Core Proof Kernel

注意，`coqc`编译器已经升级命名为`rocq`

## Structure



## Setup

To use this project, you will need to install some specific dependencies.

### Setup using `opam`

We assume that you have `opam` installed on your system. Setup instructions can be found here: https://opam.ocaml.org/doc/Install.html

```sh
opam --version
opam update
```

#### Setup instructions for working on DOML-rocq

0. `cd` into the directory containing this README.
1. Create a new opam switch for DOML-rocq:
```
opam switch create doml-rocq --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
opam switch doml-rocq
opam repo add rocq-released https://rocq-prover.org/opam/released
```

2. Install the necessary dependencies:
```
opam pin add rocq-core 9.1.0
opam pin add rocq-prover 9.0.0
opam update
opam install vsrocq-language-server.2.3.4 # for VsRocq Extension
```

3. start rocq env

```sh
opam switch doml-rocq
eval $(opam env)

# Windows Powershell
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
```

## Using interactive Rocq-prover tools

You can interactively look at the generated Rocq code using a Rocq plugin like Rocqtail, VSRocq, Proof General, or RocqIDE for the editor of your choice.

If you are using VSRocq extension in VSCode, here is a recommended setting: (.vscode/settings.json)
```
{
	"// VsRocq Extension Configuration (rocq-prover.vsrocq)": "",
	"// Modify this line to your Path to the Rocq top-level executable": "",
	"vsrocq.path": "~/.opam/doml-rocq/bin/vsrocqtop",
	"// Automatic _CoqProject detection": "",
	"// VsRocq will automatically find and use _CoqProject in workspace root": "",
	"// Leave 'vsrocq.args' empty to enable auto-detection": "",
	"// File Associations": "",
	"files.associations": {
		"*.v": "rocq"
	},
	"// Logging and Debugging": "",
	"vsrocq.trace.server": "verbose",
	"vsrocq.trace.client": "verbose",
	"// Workspace and Editor Settings": "",
	"vsrocq.proof.workspaceRoot": "${workspaceFolder}",
	"// Enable automatic compilation when files are saved": "",
	"vsrocq.autoCompile": true,
	"// Proof checking mode and delay": "",
	"vsrocq.check.mode": "async",
	"vsrocq.proof.delay": 500,
	"// Code Editing Preferences for .v files": "",
	"[rocq]": {
		"editor.tabSize": 2,
		"editor.insertSpaces": true,
		"editor.formatOnSave": false,
		"editor.defaultFormatter": null
	},
	"// Global Editor Settings (affects all languages)": "",
	"editor.formatOnSave": false,
	"editor.formatOnPaste": false,
	"// End of configuration": ""
}

```

## Compile on Windows

```sh
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
rocq compile -Q Core DOMLCore Core/Syntax.v
rocq compile -Q Core DOMLCore Core/Context.v
rocq compile -Q Core DOMLCore Core/Substitution.v
rocq compile -Q Core DOMLCore Core/Typing.v
rocq compile -Q Core DOMLCore Core/Operational.v
rocq compile -Q Core DOMLCore Core/Automation.v
rocq compile -Q Core DOMLCore Core/Lemmas.v
rocq compile -Q Core DOMLCore Core/Metatheory.v
rocq compile -Q Core DOMLCore Core/DOMLCore.v
```

## Compile on Linux

```
./run_make.sh
./clean_all.sh
```

