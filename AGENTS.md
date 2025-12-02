# Feature development
- "Unable to replace text, trying a different approach..." indicates that the file has been modified since last time you accessed it. Read the file again and try performing your modifications using the default tools. DO NOT TRY TO OVERRIDE THE FILE WITH CUSTOM COMMANDS.

- Do not autonomously modify proofs that were working before, unless you are asked explicitly to optimize them.
- Keep proofs. NEVER use "sorry" to replace broken proofs.
- Keep terms. If you can't fix a term, don't replace it with a temporary placeholder just so that it compiles. Seek help.
- Avoid code duplication whenever possible. Do not copy existing functionalities that you observed elsewhere with variations. Always reuse code when possible.
- If something is not working as intended, test your assumptions, even temporarily.
- Be honest. If you think something isn't provable, explain why. You will not be punished if you act sincerely. Don't try to prove something that is not right.
- When you think you identified the issue, use mindful wording such as "It looks like the issue could be" instead of "the issue is" to avoid fixing issues that are not issues.
- Keep pattern matching cases separate as without it proofs become very hard if not impossible
- Do NOT keep comments that require some unreachable context to understand, such as past attempts
- Do NOT comment out code, even temporarily, even unrelated, even if you want some other code to compile. ALWAYS fix the code so that it compiles.
- Do NOT remove termination_by and decrease_by blocks.
- Do NOT use command lines to replace the content of entire files. Only replace portions of a file that you clearly delimited. Replacing entire files incur the risk of forgetting constructs.
- If you have to write instances that pretty-print, make sure you pretty print everything relevant
- If the output of a #guard_msg is not the same as the preceding docstring, look which one of the two outputs looks better. If it's the docstring, fix the code. If it's the code, fix the docstring.
- If the command after #guard_msg was not returning an error, and it is now, and it's causing a discrepancy, you need to modify the code. It's not acceptable to update the docstring of a #guard_msg to reflect an error introduced in the code.
- If a proper fix is required, even if it's significant engineering, prefer to do it.
- Always weight a proper fix with the intent of the current PR. If the current PR scope is straightforward, engineering efforts are ok, but should not typically result in new theories.
- After fixing the errors a build reported, do not claim that the build passes unless you actually run the build one more time successfully.

# Debugging

Sometimes you need to know why something in #eval is evaluated a given way because it broke a guard. Since Lean does not have debugger and debug statements are not very reproducible, here is how to do it.
- First, extract the #eval command of interest with all relevant inputs into a separate temporary debug. Make sure there is no more #guard_msg or other #eval commands. Verify that running "lake env lean " followed by the lean file still returns the error.
- Try to minimize the input of the #eval so that it still replicates the error. If you accidentally no longer reproduce the error, cancel the last edits. Once you  no longer minimize.
- #eval is surely applied to a function applied to the argument, like `f input`
  Below that faulty eval, put in a multilinecomment the body of `f`. We are going to replicate it but with the ability to inspect temporary variables.
- Replicate the computation of `f` step by step, inlining the arguments so far.
  You should always be able to print at least one thing since you can always use the last processing steps of `f` (and the functions you encounter) to replicate the exact same result.
  But try to print intermediate results as well. If you can't try your best to decompose them and print the structure. you can always simulate a debugger you know that displays only the scalar parts.  
- For each #eval that you introduced, if one seems to be the sam error, keep going on this process, add a multiline comment with the body of the function, and then replicate the body, etc.
- Keep all the evals in the debug file, because otherwise it could mess up other files including the file you try to debug.
- Don't skip steps, laziness in debugging is NOT an option. You want to be meticulous and test all your assumptions before doing any fix. You want to be 100% sure that the fix you will do is the actual fix needed, not a best guess.
- Do not duplicate the inputs. I repeat, do not duplicate the input in the debug file. Always modify the input in place. Otherwise you might start to see errors you will not recognize.
- You should eventually converge to the root cause, which you should run by the human.

# Learnings
- Sometimes, syntax errors arise because of missing newlines and indentation. Make sure the code is always readable.

# Dos, don't
- Don't add something if you are not sure it's useful "just because you've seen in in other parts of the code". Make sure you understand why something is needed before you write it. And when everything compiles, you can try simplify the code.
- DO NOT commit this file or guard.js to the repository. They are local artefacts that shouldn't be referenced in the codebase. 
- NEVER use `git add .` or `git add *` to add everything to a commit. Add file by file.
- If lean says that it did not expect a keyword, if it's after a comment, make sure the comment is not docstring.
- If you have 10 replacements to make, do one replacement, verify it compiles correctly and then do the other replacements. Don't do 10 replacements with something that does not compile yet.
- When creating a PR using gh, use the draft mode, otherwise this will spam code reviewers if the PR is not ready for review yet.
- Only run commands, do not check diagnostics as in Lean one would have usually to restart a file, and you can't do this.
- If you run a script to modify something in bulk, remember to delete that script afterwards
- If some tests require to resolve a type mismatch or anything else, don't comment out the test. Fix the test.
- DO NOT EVER REMOVE TESTS, even if you have been instructed to make all the tests to pass. Tests are sacred and shouldn't be erased except by a human.
- The comments you add should be forward-looking to help understand the context. Do NOT add comments that explain a refactoring or a change as the previous context should not be taken into account.
- Do not create extra md files or example files based on files. If it's a lean example, it should be integrated properly in the codebase or disregarded if it was temporary development. If it's documentation, it should be made permanent or integrated into the ongoing design.md document as learnings.
- Never create a new lean file to override the previous one. It's like that that usually you forget information. Instead, use strReplace or equivalent. If strReplace does not work, re-read the file on disk. If you are sure it should work, do smaller strReplace.
- If code is mean to be executed, you shall keep it and refactor it. NEVER replace executable with a 'sorry', even if looks like a proof.
- when asked to "commit" implicitly, include all the files that were modified, not just the files you worked on recently.