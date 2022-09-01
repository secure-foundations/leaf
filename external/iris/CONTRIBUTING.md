# Contributing to the Iris Coq Development

Here you can find some how-tos for various thing sthat might come up when doing
Iris development.  This is for contributing to Iris itself; see
[the README](README.md#further-resources) for resources helpful for all Iris
users.

To work on Iris itself, you need to install its build-dependencies.  Again we
recommend you do that with opam (2.0.0 or newer).  This requires the following
two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make builddep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update Iris, do `git pull`.  After an update, the development may fail to
compile because of outdated dependencies.  To fix that, please run `opam update`
followed by `make builddep`.

## How to submit a merge request

To contribute code, you need an MPI-SWS GitLab account as described on the
[chat page](https://iris-project.org/chat.html).  Then you can fork the
[Iris git repository][iris], make your changes in your fork, and create a merge
request.  If forking fails with an error, please send your MPI-SWS GitLab
username to [Ralf Jung][jung] to unlock forks for your account.

Please do *not* use the master branch of your fork, that might confuse CI.  Use
a feature branch instead.

[jung]: https://gitlab.mpi-sws.org/jung
[iris]: https://gitlab.mpi-sws.org/iris/iris

## How to update the std++ dependency

* Do the change in std++, push it.
* Wait for CI to publish a new std++ version on the opam archive, then run
  `opam update iris-dev`.
* In Iris, change the `opam` file to depend on the new version.
  (In case you do not use opam yourself, you can see recently published versions
  [in this repository](https://gitlab.mpi-sws.org/iris/opam/commits/master).)
* Run `make builddep` (in Iris) to install the new version of std++.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.

## How to write/update test cases

The files in `tests/` are test cases.  Each of the `.v` files comes with a
matching `.ref` file containing the expected output of `coqc`.  Adding `Show.`
in selected places in the proofs makes `coqc` print the current goal state.
This is used to make sure the proof mode prints goals and reduces terms the way
we expect it to.  You can run `make MAKE_REF=1` to re-generate all the `.ref` files;
this is useful after adding or removing `Show.` from a test.  If you do this,
make sure to check the diff for any unexpected changes in the output!

Some test cases have per-Coq-version `.ref` files (e.g., `atomic.8.8.ref` is a
Coq-8.8-specific `.ref` file).  If you change one of these, remember to update
*all* the `.ref` files.

If you want to compile without tests run `make NO_TEST=1`.

## How to build/install only one package

Iris is split into multiple packages that can be installed separately via opam.
You can invoke the Makefile of a particular package by doing `./make-package
$PACKAGE $MAKE_ARGS`, where `$MAKE_ARGS` are passed to `make` (so you can use
the usual `-jN`, `install`, ...).  This should only rarely be necessary. For
example, if you are not using opam and you want to install only the `iris`
package (without HeapLang, to avoid waiting on that part of the build), you can
do `./make-package iris install`.  (If you are using opam, you can achieve the
same by pinning `coq-iris` to your Iris checkout.)

Note that `./make-package` will never run the test suite, so please always do a
regular `make -jN` before submitting an MR.

## How to test effects on reverse dependencies

The `iris-bot` script makes it easy to test the effect of a branch on reverse
dependencies. It can start tests ensuring they all still build, and it can do
comparative timing runs.

If you have suitable permissions, you can trigger these builds yourself.
But first, you need to do some setup: you need to create a GitLab access token
and set the `GITLAB_TOKEN` environment variable to it. Go to
<https://gitlab.mpi-sws.org/-/profile/personal_access_tokens>, pick a suitable
name (such as "iris-bot"), select the "api" scope, and then click "Create
personal access token". Copy the value it shows and store it in some suitable
place; you will not be able to retrieve this value from GitLab in the future!
For example, you could create a `.env` file in your Iris clone containing:
```
export GITLAB_TOKEN=<your token here>
```
Then you can easily get the token back into the environment via `. .env`.

Once that setup is done, you can now use `iris-bot`. Set at least one of
`IRIS_REV` or `STDPP_REV` to control which branches of these projects to build
against (they default to the default git branch). `IRIS_REPO` and `STDPP_REPO`
can be used to control the repository in which the branch is situated. Setting
`IRIS` to "user:branch" will use the given branch on that user's fork of Iris,
and similar for `STDPP`.

Supported commands:
- `./iris-bot build [$filter]`: Builds all reverse dependencies against the
  given branches. The optional `filter` argument only builds projects whose
  names contains that string.
- `./iris-bot time $project`: Measure the impact of this branch on the build
  time of the given reverse dependency. Only Iris branches are supported for
  now.

Examples:
- `IRIS_REV=myname/mybranch ./iris-bot build` builds *all* reverse dependencies
  against `myname/mybranch` from the main Iris repository.
- `IRIS=user:branch ./iris-bot build examples` builds the [examples] against
  the `branch` in `user`'s fork of Iris.
- `IRIS_REV=myname/mybranch ./iris-bot time examples` measures the timing impact
  of `myname/mybranch` from the main Iris repository on the [examples].

[examples]: https://gitlab.mpi-sws.org/iris/examples
