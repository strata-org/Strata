* When using `git add`, always verify first what files were created, modified or deleted with `git status` and only add files relevant to the work you did.
*  Unless explicitly instructed, always check that the build passes before committing anything.
* Unless explicitly instructed, always check that the tests pass before pushing anything.
* If you have 10 replacements to make, do one replacement, verify it compiles correctly and then do the other replacements. Don't do 10 replacements with something that does not compile yet.
* Unless explicitly instructed, when creating a PR with gh, create it in draft mode.
* If you run a script to modify something in bulk, remember to delete that script afterwards.
* Unless explicitly instructed, NEVER comment out tests "for now". If tests are not passing, fix them.
* Unless explicitly instructed, NEVER update the output of a test so that it matches an error that did not exist. If a test was succeeding before, it's almost certain that the test outputing an error is a bug to fix, not a test output to update.
* Unless explicitly instructed, NEVER ever remove tests. Tests are sacred. Never edit existing tests without the permission of the user.
* Always use stateless comments that don't need to comment about the previous state of the code
* Lean examples should be integrated properly in the codebase or disregarded if it was temporary development. Documentation items should be made permanent in lean files or in the documentation folder, not as stand-alone extra md files anywhere.
* When creating PR descriptions, always run the description through the human first. Be concise. The PR description should focus on what the PR delivers, not the journey to get there. Explain briefly what the problem was, how the PR solves it. Don't mention files. You can say how it was tested briefly (existing tests pass, new tests added...). Don't mention commit numbers.
*  Use a temporary file for the PR description to avoid artefacts in formatting a PR description from the command line.
* Never use fsWrite to overwrite an existing file, unless explicitly instructed. Always use strReplace to make targeted changes. Before using fsWrite on any path, check if the file exists by reading it first - if it exists and you need to modify it, use strReplace instead. If strReplace fails with 'string not found', re-read the file from disk to see what changed, then use strReplace with the updated content. If you're certain strReplace should work but it's failing, try smaller, more specific replacements."
* If code is mean to be executed (a def or private def, not a theorem), you shall keep its body. NEVER replace executable with a 'sorry', even if looks like a proof. Tests will not run otherwise. At best you should ask the user.
* If the user requires something more complex than you anticipated, never revert the changes you did so far, unless you have a clear plan to reimplement it and not simplify it to the point that it's not what was asked. What a user asked should be completed.
* Our project has CI checks so know that all tests are always passing on the branch main as a comparison in case tests suddenly fail. There is never a pre-existing failing test
* When two or more cases of a pattern matching are similar, you should create a helper to reduce code duplication.
* When refactoring the bodies of similar functions, you might end up with functions that have a one liner body. In that case, it's often preferable to inline them rather than keeping them around.
* When merging and investigating a conflict in a file, NEVER fully accept the branch's file or main's file, as that would potentially break issues that were fixed.
* When not on main and asked to pull main, overwrite main with `git fetch origin main:main`
* When writing code that builds a list, build the list in reverse and then reverse it at the end.
* Before claiming that a PR is ready, spawn an agent whose task will be to review the PR in search for code duplication, useless code, weird constructs. Suggest the user to do that too.
* When reverting a change, do not use git checkout on a file. Instead, use the standard API strReplace, or at least diff the file with HEAD to ensure you don't accidentally erase previous fixes
* When you get "aborting evaluation since the expression depends on the 'sorry' axiom", it's not always explicit `sorry`. Compilation errors and resolution errors are also replaced by ` sorry` internally. Make sure you have an error context large enough. The first error is often the most important to fix first.
* Code degrading, even if it helps to compile the code after a refactoring, requires explicit approval. Examples of code degrading are replacing formatting by constant strings, simplifying strings, removing comments.
* If you are solving a git conflict and you see that remote deleted some code you had been modifying, always search for places where the code might have migrated. You can study the log of git and git messages to understand better what might have happened
* Always make sure the code compile in the order it's intended. Never comment out parts, never replace proofs by sorry, just to move on to the next part. If something does not compile, there is no point to "check if the rest compiles".

* Only use the command line build tool to check whether your changes are correct. The IDE diagnostics can often need refresh.
* While modifying code, only build one file at a time. Don't trigger the build on the whole project until you are done with all changes, because builds timeout after 60 seconds.
* When realizing that a task requires something that a previous task should have done but was not done, take ownership and finish that other task that should have been done in the first place.
* Do not use grep, cat or other command line tools other than the API except if it's really necessary. All these command-line tools require approval and slow down the development. Use the API as much as possible
* When executing "lake build", if you are not on a cloud desktop, prefix your command with the equivalent of "set LEAN_NUM_THREADS=4 & " so that you are not using all the cores of the machine.
* If you see the result of a command like "it: not found" when you wrote "git" something, it's an IDE bug. Same for "et: not found" if you wrote "set". Retry the command, usually it works the second time.


* When fixing a failing proof with repetitive structure (like `repeat` or `all_goals`), don't just look at the final error state. Extract the body of the repeat/loop, test it on a single case to understand what works, adjust the tactics based on what you learn, then put the fixed version back into the repeat. Use `rotate_left`, `rotate_right`, or `swap` to reorder goals when needed to solve them in a more convenient order. Browse the entire proof to understand the pattern before attempting fixes.



* When fixing a failing proof or investigating a proof, use the tactic `trace_state `in various places so that you can see the proof state in places where you are not expected to know the proof state, not just in places where it is failing. If really stuck, you can also use `trace_ state` on original proofs of main since they were all passing, so that you understand how it was proved. That will be immensely helpful
