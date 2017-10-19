Code of conduct for contributors
================================

All contributors are encouraged to follow the code style recommendations, and are required to follow the outlined branching system. These guidelines are outlined in the following sections.

Code style recommendations
==========================

Background
----------

UxAS grew out of numerous research project and can still seem pieced
together. A similar style across the code base can make it easier to
navigate through the software. A list of our preferred style and best
practices are captured in two documents:

-   [Practices](run:../../doxygen/files/CppProgrammingPracticesGuide.html)

-   [Style](run:../../doxygen/files/CppProgrammingStyleGuide.html)

The top guidelines are as follows:

-   Use smart pointers, never bare

-   Use the full namespace for clarity

-   Minimize logic in constructors

-   Use C++11 types (e.g. int32\_t rather than int)

-   Prefix member variables with ‘m\_’

-   Booleans start with a verb, i.e. isOpen

-   Use abbreviations sparingly

-   Any complex logic should be in the .cpp file, not the .h

-   Use 4 spaces instead of tab

-   Append units to variable names (e.g. distance\_m)

-   Braces on own lines

-   Keep parameters local, not in global files

-   Document with Doxygen comments

Branch description and git flow expectations
============================================

The OpenUxAS branching model addresses the following concerns:

-   We have a stable branch that always builds and passes tests

-   Multiple collaborative teams can proceed with their development
    independently

-   Discrete features can be contributed to the main line of OpenUxAS
    development, and these can be integrated into other teams’ ongoing
    work

-   Until OpenUxAS is public, all teams can use the `afrl-rq`
    organization’s Travis-CI account for continuous integration

To address these concerns, OpenUxAS uses a variant on the [Git
Flow](http://nvie.com/posts/a-successful-git-branching-model/), [GitLab
Flow](https://docs.gitlab.com/ee/workflow/gitlab_flow.html), and [GitHub
flow](https://guides.github.com/introduction/flow/) models.

Because OpenUxAS does not yet have a fixed cycle of releases, we do not
need the additional complexity of `hotfix/` and `release/` branches
present in Git Flow. However, since a number of collaborating teams work
on OpenUxAS simultaneously, it makes sense to have long-lived branches
for each team, rather than only having feature branches and a stable
branch.

This README does not go into detail about the various Flow models, but
instead provides instructions for common scenarios. We encourage you to
read about the Flow models to get more of a sense for the “why”; here we
are focusing on the “how”.

Quick Overview
--------------

The repository will typically have a branching structure like the
following:

-   `master`

-   very stable, only updated by pull request from `develop`

-   `develop`

-   stable, only updated by pull request from feature branches

-   `teamA`

-   team branch for Team A

-   stable at the discretion of Team A

-   updated by merging in feature branches and `develop`

-   `teamA-feature1`

-   feature branch for Team A

-   when finished, merged into `develop` via pull request

-   `teamB`

-   `teamB-feature1`

-   etc.

Team Branches
-------------

The team branch is the branch off of which your team will work. It
serves the role of the `develop` branch of Git Flow or the `master`
branch of GitLab and GitHub Flow. This branch is never intended to be
directly merged back into `develop`, but feature branches based off of
it will be.

If you have experience with these models, this concept probably seems
odd. Eventually, we would like to replace these team branches with
entire repo forks for each team, but until OpenUxAS is public, this
would prevent forks from using the `afrl-rq` Travis-CI account.

### Creating

Start by creating a new branch that will serve as the active development
branch for your team. This step should only be necessary once for your
team; this branch is meant to be long-lived as opposed to a feature
branch that is quickly merged in and deleted.

    $ git checkout develop
    $ git checkout -b teamA

### Updating

You will want to regularly incorporate the latest changes from the
`develop` branch in your team branch. This reduces the pain when merging
your team’s changes back into `develop`.

Start by making sure your local `develop` branch is up-to-date:

    $ git checkout develop
    $ git pull

Then merge the updated `develop` with your team branch:

    $ git checkout teamA
    $ git merge develop

Feature Branches
----------------

Feature branches are shorter-lived branches meant to encompass a
particular effort or feature addition. These branches will be the means
for you to incorporate your team’s changes into the main `develop`
branch via pull requests.

Feature branches will always be based off of your team branch, so if
your team branch has commits you would like to see in `develop`, you can
simply create a new feature branch and begin the pull request process
right away.

### Naming

To help the OpenUxAS maintainers know which branches belong to which
teams, feature branches should be named using your team name as a
prefix, for example `teamA-feature1`.

### Creating

Create a feature branch by checking it out off of your team branch. Note
that it will save you some effort at the later merge to update your team
branch from `develop` first.

    $ git checkout teamA
    $ get checkout -b teamA/feature1

### Merging to Team Branch

For a long-running feature branch, you may want to occasionally merge it
back into your team branch so it can be shared within your team before
it’s ready to be merged into `develop`.

    $ git checkout teamA
    $ git merge teamA/feature1

### Merging to develop

You cannot directly merge a feature branch into `develop`, because it is
protected. Instead, open a pull request from the feature branch into
`develop`, and your changes will be merged after review.

It is a good idea to update your team branch and delete your feature
branch once it is merged into `develop`.

    $ git checkout develop
    $ git pull
    $ git checkout teamA
    $ git merge develop
    $ git push origin --delete teamA/feature1
    $ git branch -d teamA/feature1
