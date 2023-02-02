# Brown CS22 Spring 2023: Lean project

## Directions for setting up GitPod

Before following these directions,
you will need to sign up for a [GitHub account](https://github.com/)
if you don't have one already.
This will be useful throughout the rest of your career at Brown CS.
We strongly recommend picking a professional and identifiable username.
For example, I'm [robertylewis](https://github.com/robertylewis).

There are scattered reports that this might not work on some versions of Safari. 
If you run into trouble, try it in Chrome or Firefox before reporting to us.

* Click on [this link](https://gitpod.io/#https://github.com/brown-cs22/CS22-Lean-2023).
  * This will send you to Gitpod.
    Log in with your GitHub account.
  * If you are given a choice to open in your browser or locally,
    choose the browser option.
* It will take a minute, but eventually,
  you'll see a VSCode interface in your browser.
  You should see:
  * A panel `Terminal` on the bottom.
    There will be some code running here at first.
    Let it finish before you do anything else;
    it's done when the last line is
    `gitpod /workspace/leanclass (main) $`.
  * A panel `Explorer` on the left that lets you browse directories and files.
  * A text editor panel in the middle.
  * A panel on the right, `Lean Infoview`.
* Go back to the [Gitpod home page](https://gitpod.io/workspaces). 
  You'll see your new workspace there.
  Use the dropdown menu ⋮ to:
  * Rename the workspace to something recognizable, like "Brown CS0220 Class Repository."
  * Pin the workspace. This is important: 
    if you don't pin it and go two weeks without opening it, Gitpod will delete it!

You're all set up.
In the future, you should bookmark your workspace URL and access it that way,
or use the Gitpod home page. 
The link above will create a new workspace each time you click it.
(This is why we recommend renaming your main workspace, to distinguish it from new ones.)

If at any point your workspace becomes unusable
and you think you need a fresh start,
you can click on the original link to get a new copy of the course workspace.

## Directions for updating 

We will push more lecture demos and homework assignments to this project throughout the semester.
To pull them into your Gitpod instance, follow these directions:

* Open the terminal in Gitpod, if it is not already open. 
* Run the command `scripts/pull-updates`.

We will try not to let this happen, but occasionally, we might change files that you have edited yourself.
The `pull-updates` script should notice this and not overwrite your changes.
But if there are conflicts, you may have to reset your work.
(Feel free to copy your changes to another file if you want.)
Running the command `scripts/reset-all` and then `pull-updates` again should clean things up.

## git: the fine print 

This is a GitHub repository, 
and your workspace will interact with our course materials using git.
We do *not* expect you to have any experience or knowledge of git
beyond having a GitHub account.
If you do know how to use git and would like to use proper version control in your workspace,
you are welcome to, but our course staff is not responsible for helping!
We document the setup here for your reference.

* We will try our best not to modify files in the `BrownCs22/Demos` directory after we add them.
  This should minimize merge conflicts if you edit files there.
* Official course materials,
  including lecture demos and homeworks,
  will be pushed to the `main` branch of this repository.
  You will have to pull these changes to your workspace.
* The `pull-updates` script in your workspace
  will `git stash` any uncommitted changes you have,
  pull our updates,
  and `git stash pop` your changes back.
  If your changes conflict with ours, 
  it will leave your project unmodified and print an error message.
  This script assumes you have not made any commits of your own;
  if you have, you're on your own!
* The `reset-all` script resets all tracked files to the most recent commit.
