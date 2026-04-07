Tasks:
* Install Lean 4 ([https://lean-lang.org/install/Links to an external site.](https://lean-lang.org/install/)). I recommend using VS Code, even if you prefer other editors like I do. An integral part of the experience is its powerful Lean 4 extension.
* Get [https://github.com/PatrickMassot/GlimpseOfLeanLinks to an external site.](https://github.com/PatrickMassot/GlimpseOfLean). You can use the "∀" menu within VS Code and do "Open Project -> Download Project". This will get everything set up for you.
  * If you want to do it manually, clone the repository, and run "lake exe cache get" from the root of the project. (If you do not have the Lean toolchain yet, the Lean extension will offer to install it for you if you open up any file in the project.
  * If the Lean extension is compiling Mathlib files, **you can download a pre-built cache**. Use the "∀" menu, and do "Project Actions -> Fetch Mathlib Build Cache". This will stop Lean, download the cache, and restart, automatically.
  * Once you have a cache, you can click "Restart File" to get Lean to build project files. You can also use "lake build" on the command line to build all the files in the project.
* Please do the four numbered exercise files in GlimpseOfLean/Exercises, and at least one of the exercise files in GlimpseOfLean/Exercises/Topics
* Post in #**personal logs** (topic: your name) about your experience.
  * Format: start with a heading with the date (e.g. `# Apr 10`) then the rest is free-form.
  * Talk about which exercises you completed, and which topic you chose. Partial progress is OK.
  * Be sure to also comment on something you found confusing, something you found fun/exciting, and something you would like to know more about.