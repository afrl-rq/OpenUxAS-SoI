#|

GE CONFIDENTIAL INFORMATION © 2017 General Electric Company 
-- All Rights Reserved. 

RAE, the Requirements Analysis Engine
Author: Pete Manolios, pmanolios@gmail.com, manolios@ge.com

Version: 2017-8-11.

I removed the rae-default-settings.lsp file and just added the
default values as comments in this file. The
rae-default-settings.lsp file was supposed to be shipped with
read-only permissions, but it seems users were modifying it, so
this changes seemed best.

Version: 2017-8-6.

Updated the default settings so that we use 32-bit words instead
of 12-bit words. The improvements to cgen allow us to do this
without any loss of analysis.

Version: 2017-7-18.

Added the *stage-computed-hint-max* parameter to this file.  If
you're using RAE on 777x, please set this parameter as per the
documentation below. Removed parameters that are no longer used
in the new preprocessor.

Removed parameters that are no longer used in the new
preprocessor.

Version: 2017-6-28.

Added the *stage-computed-hint-max* parameter to this file.  If
you're using RAE on 777x, please set this parameter as per the
documentation below.

Version: 2017-3-2.

Added some minor comments.

Version: 2017-1-26.

In an effort to make it easy to customize RAE per project or per
user, this file includes the top-level parameters that can be
used to control how RAE processes requirements.

Please read through this file and set the parameters in a way
that makes sense for your project.

Changing parameters is easy: just update this file and rerun 
RAE.

If you want to revert back to the default settings, look
at the file rae-default-settings.lsp.

Tools team: make rae-default-settings.lsp read only in ASSERT.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; PRIMARY PARAMETERS
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#|

The number of bits used to represent integers whose size is not
specified in the ontology.

*word-size* determines the default range for numeric types, which
is -2^(*word-size*-1)..2^(*word-size*-1)-1, the typical range for
n-bit 2's complement integers. The same range is used for
rationals, but of course any rational in the range is allowed.

The default value is 32.

|#

(defparameter *word-size* 32)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; SECONDARY PARAMETERS
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

The parameter *stage-computed-hint-max* is used to control how
many times we allow the same data definition to be expanded in a
goal.

Projects with decomposition forms should keep this number low,
which allows us to avoid the generation of potentially many
subgoals during testing when looking for a counterexample, since
counterexamples are not likely to be found due to the undefined
decomposition functions.

For the 777X project, set this value to 1000.

The default value is 4.
|#

(defparameter *stage-computed-hint-max* 4)
