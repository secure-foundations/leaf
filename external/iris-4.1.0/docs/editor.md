Here we collect some information on how to set up your editor to properly input
and output the unicode characters used throughout Iris.

If you really want to, you can also avoid having to type unicode characters by
importing `iris.bi.ascii`.  That enables parsing-only ASCII alternatives to many
unicode notations. (Feel free to report an issue when you notice that a notation
is missing.)  The easiest way to learn the ASCII syntax is to
[read this file](/iris/bi/ascii.v).
Note however that this will make your code harder to read and work on for Iris
developers that are used to our default unicode notation---generally, our
recommendation is to use the unicode syntax whenever possible. In particular,
Unicode syntax is required for MRs to Iris itself and other Iris-managed
repositories.

## General: Unicode Fonts

Most editors will just use system fonts for rendering unicode characters and do
not need further configuration once the fonts are installed.  Here are some
combinations of fonts that are known to give readable results (i.e., each of
these sets of fonts covers all the required characters):

* Fira Mono, DejaVu Mono, Symbola

## Emacs

### Unicode Input

First, install `math-symbol-lists` by doing `M-x package-install math-symbol-lists`.

Next, add the following to your `~/.emacs` to configure an input method based
on the math symbol list, and with some custom aliases for symbols used a lot in Iris:
```
;; Input of unicode symbols
(require 'math-symbol-lists)
; Automatically use math input method for Coq files
(add-hook 'coq-mode-hook (lambda () (set-input-method "math")))
; Input method for the minibuffer
(defun my-inherit-input-method ()
  "Inherit input method from `minibuffer-selected-window'."
  (let* ((win (minibuffer-selected-window))
         (buf (and win (window-buffer win))))
    (when buf
      (activate-input-method (buffer-local-value 'current-input-method buf)))))
(add-hook 'minibuffer-setup-hook #'my-inherit-input-method)
; Define the actual input method
(quail-define-package "math" "UTF-8" "Ω" t)
(quail-define-rules ; add whatever extra rules you want to define here...
 ("\\fun"    ?λ)
 ("\\mult"   ?⋅)
 ("\\ent"    ?⊢)
 ("\\valid"  ?✓)
 ("\\diamond" ?◇)
 ("\\box"    ?□)
 ("\\bbox"   ?■)
 ("\\later"  ?▷)
 ("\\pred"   ?φ)
 ("\\and"    ?∧)
 ("\\or"     ?∨)
 ("\\comp"   ?∘)
 ("\\ccomp"  ?◎)
 ("\\all"    ?∀)
 ("\\ex"     ?∃)
 ("\\to"     ?→)
 ("\\sep"    ?∗)
 ("\\lc"     ?⌜)
 ("\\rc"     ?⌝)
 ("\\Lc"     ?⎡)
 ("\\Rc"     ?⎤)
 ("\\lam"    ?λ)
 ("\\empty"  ?∅)
 ("\\Lam"    ?Λ)
 ("\\Sig"    ?Σ)
 ("\\-"      ?∖)
 ("\\aa"     ?●)
 ("\\af"     ?◯)
 ("\\auth"   ?●)
 ("\\frag"   ?◯)
 ("\\iff"    ?↔)
 ("\\gname"  ?γ)
 ("\\incl"   ?≼)
 ("\\latert" ?▶)
 ("\\update" ?⇝)

 ;; accents (for iLöb)
 ("\\\"o" ?ö)

 ;; subscripts and superscripts
 ("^^+" ?⁺) ("__+" ?₊) ("^^-" ?⁻)
 ("__0" ?₀) ("__1" ?₁) ("__2" ?₂) ("__3" ?₃) ("__4" ?₄)
 ("__5" ?₅) ("__6" ?₆) ("__7" ?₇) ("__8" ?₈) ("__9" ?₉)

 ("__a" ?ₐ) ("__e" ?ₑ) ("__h" ?ₕ) ("__i" ?ᵢ) ("__k" ?ₖ)
 ("__l" ?ₗ) ("__m" ?ₘ) ("__n" ?ₙ) ("__o" ?ₒ) ("__p" ?ₚ)
 ("__r" ?ᵣ) ("__s" ?ₛ) ("__t" ?ₜ) ("__u" ?ᵤ) ("__v" ?ᵥ) ("__x" ?ₓ)
)
(mapc (lambda (x)
        (if (cddr x)
            (quail-defrule (cadr x) (car (cddr x)))))
      (append math-symbol-list-basic math-symbol-list-extended))
```

Finally, set your default input method with `M-x customize-set-value`, setting
`default-input-method` to `math`.

### Font Configuration

Even when usable fonts are installed, Emacs tends to pick bad fonts for some
symbols like universal and existential quantifiers.  The following configuration
results in a decent choice for the symbols used in Iris:

```
;; Fonts
(set-face-attribute 'default nil :height 110) ; height is in 1/10pt
(dolist (ft (fontset-list))
  ; Main font
  (set-fontset-font ft 'unicode (font-spec :name "Monospace"))
  ; Fallback font
  ; Appending to the 'unicode list makes emacs unbearably slow.
  ;(set-fontset-font ft 'unicode (font-spec :name "DejaVu Sans Mono") nil 'append)
  (set-fontset-font ft nil (font-spec :name "DejaVu Sans Mono"))
)
; Fallback-fallback font
; If we 'append this to all fontsets, it picks Symbola even for some cases where DejaVu could
; be used. Adding it only to the "t" table makes it Do The Right Thing (TM).
(set-fontset-font t nil (font-spec :name "Symbola"))
```

### Automated Indentation

The default indentation configuration of company-coq is not compatible with the Iris syntax.
As a result, automatic indentation will indent lines incorrectly.

To solve some of these indentation errors you can add the following line to your Emacs
initialisation file:
```
(setq coq-smie-user-tokens
   '(("," . ":=")
	("∗" . "->")
	("-∗" . "->")
	("∗-∗" . "->")
	("==∗" . "->")
	("=∗" . "->") 			;; Hack to match ={E1,E2}=∗
	("|==>" . ":=")
	("⊢" . "->")
	("⊣⊢" . "->")
	("↔" . "->")
	("←" . "<-")
	("→" . "->")
	("=" . "->")
	("==" . "->")
	("/\\" . "->")
	("⋅" . "->")
	(":>" . ":=")
	("by" . "now")
	("forall" . "now")              ;; NB: this breaks current ∀ indentation.
   ))
```
This will let the indentation strategy treat the Iris symbols (e.g. `-∗`) similar to the
closely related Coq symbols (e.g. `->`).
Note that `->` is used in many places, as its indentation behaviour is:
```
  P ->
  Q
```
This is the indentation behaviour is what we want, e.g. for `∗`:
```
  P ∗
  Q
```
Note that this configuration has some caveats.
Notably, the change to `forall` (which gives good behavior to e.g.
`iInduction xs as [|x xs IHxs] forall (ys).`), now gives the following indentation
behavior to universal quantification:
```
  ∀ x,
  P x
```
This is not what we want; the second line should be indented by 2 spaces.

## CoqIDE 8.9 and earlier on Linux (ibus-m17n)

On Linux with old versions of CoqIDE you can use the Intelligent
Input Bus (IBus) framework to input Unicode symbols. First, install `ibus-m17n`
via your system's package manager. Next, create a file `~/.m17n.d/coq.mim` to
configure an input method based on the math symbol list, and with some custom
aliases for symbols used a lot in Iris as defined [here](ibus).

To use this input method, you should:

1. Enable the "Coq" input using your system settings or using the IBus
   configuration tool. The Coq input method typically appears in the category
   "other".
2. On some systems: In CoqIDE, you have to enable the input method by performing
   a right click on the text area, and selecting "System (IBus)" under "input
   method".

## CoqIDE 8.10+ Unicode input

Instead of configuring the input system-wide, you can use CoqIDE's support for
inputting Unicode symbols (introduced in Coq v8.10). To input a symbol, type a
LaTeX-like escape sequence, for example `\alpha` and then type
`<Shift>-<Space>`, which will expand it into `α`. Expansion will work on a
prefix of the command as well. You can also customize the expansion keyboard
shortcut, which is under Tools/LaTeX-to-unicode.

This system is configurable by adding a Unicode bindings file with additional
expansion sequences. On Linux this file should go in
`~/.config/coq/coqide.bindings` while on macOS it should go in
`~/Library/Application Support/Coq/coqide.bindings` (or under `$XDG_CONFIG_HOME`
if you have that set).

Here is a `coqide.bindings` file for a variety of symbols used in Iris:

```
# LaTeX-like sequences are natively supported (eg, \forall, \mapsto)
# Iris-specific abbreviations
\fun            λ
\mult           ⋅ 1
\ent            ⊢ 1
\valid          ✓
\diamond        ◇
\box            □ 1
\bbox           ■
\later          ▷
\pred           φ
\and            ∧
\or             ∨
\comp           ∘ 1
\ccomp          ◎
\all            ∀
\ex             ∃
\to             →
\sep            ∗
\lc             ⌜ 1
\rc             ⌝ 1
\Lc             ⎡ 1
\Rc             ⎤ 1
\lam            λ
\empty          ∅
\Lam            Λ
\Sig            Σ
\-              ∖ 1
\aa             ● 1
\af             ◯ 1
\auth           ●
\frag           ◯
\iff            ↔ 1
\gname          γ
\incl           ≼
\latert         ▶
\update         ⇝
# accents
\"o             ö
\Lob            Löb
# subscripts and superscripts
\^+             ⁺
\_+             ₊
\^-             ⁻
\_0             ₀
\_1             ₁
\_2             ₂
\_3             ₃
\_4             ₄
\_5             ₅
\_6             ₆
\_7             ₇
\_8             ₈
\_9             ₉
\_a             ₐ
\_e             ₑ
\_h             ₕ
\_i             ᵢ
\_k             ₖ
\_l             ₗ
\_m             ₘ
\_n             ₙ
\_o             ₒ
\_p             ₚ
\_r             ᵣ
\_s             ₛ
\_t             ₜ
\_u             ᵤ
\_v             ᵥ
\_x             ₓ
```

## Visual Studio Code

### VSCoq setup

The recommended extension as of December 2019 is [Maxime Dénès's
VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).
Press `Ctrl Shift P` or `Cmd Shift P` and then type "coq" to see the list of Coq
commands and keyboard shortcuts.

### Font setup

To use unicode you need a font that supports all the symbols, such as [Fira
Code](https://github.com/tonsky/FiraCode/wiki/Installing). Download and install
the font, and in VS Code press `Cmd ,` or `Ctrl ,` to go to the settings, search
for "font", and use "FiraCode-Retina" on macOS or "Fira Code Retina" on Linux as the font-family and optionally enable
ligatures.

### Unicode input setup

Install the [Generic input method
extension](https://marketplace.visualstudio.com/items?itemName=mr-konn.generic-input-method).
To insert a symbol, type the code for a symbol such as `\to` and then press
`Space` or `Tab`. To enable Iris unicode input support, open your user settings,
press `Cmd ,` or `Ctrl ,`, type "generic-input-methods.input-methods", and then
click on "Edit in settings.json" and add the contents of [this file](vscode).

## Vim

The [Coqtail](https://github.com/whonore/coqtail) plugin can be used to develop Coq code in `vim` (install it with your favorite plugin manager).
Follow the installation instructions in Coqtail's README to setup your keybinds and find out about its usage.

### Unicode support
For Unicode support, make sure that your terminal emulator supports Unicode and configure it to use a font with Unicode support.

For entering Unicode symbols, one option is the plugin [latex-unicoder](https://github.com/joom/latex-unicoder.vim).
Install it with your favorite plugin manager.
To enter a Unicode symbol, hit `C-l` in normal or insert mode. For more details on the usage, see its README.

latex-unicoder comes with a large set of pre-configured symbols known from LaTeX, but you can also add your own by adding (and adapting) the following to your `.vimrc`:
```
let g:unicode_map = {
  \ "\\fun"     :   "λ",
  \ "\\mult"    :   "⋅",
  \ "\\ent"     :   "⊢",
  \ "\\valid"   :   "✓",
  \ "\\diamond" :   "◇",
  \ "\\box"     :   "□",
  \ "\\bbox"   	:   "■",
  \ "\\later"  	:   "▷",
  \ "\\pred"   	:   "φ",
  \ "\\and"    	:   "∧",
  \ "\\or"     	:   "∨",
  \ "\\comp"   	:   "∘",
  \ "\\ccomp"  	:   "◎",
  \ "\\all"    	:   "∀",
  \ "\\ex"     	:   "∃",
  \ "\\to"     	:   "→",
  \ "\\sep"    	:   "∗",
  \ "\\lc"     	:   "⌜",
  \ "\\rc"     	:   "⌝",
  \ "\\Lc"     	:   "⎡",
  \ "\\Rc"     	:   "⎤",
  \ "\\lam"    	:   "λ",
  \ "\\empty"  	:   "∅",
  \ "\\Lam"    	:   "Λ",
  \ "\\Sig"    	:   "Σ",
  \ "\\-"      	:   "∖",
  \ "\\aa"     	:   "●",
  \ "\\af"     	:   "◯",
  \ "\\auth"   	:   "●",
  \ "\\frag"   	:   "◯",
  \ "\\iff"    	:   "↔",
  \ "\\gname"  	:   "γ",
  \ "\\incl"   	:   "≼",
  \ "\\latert" 	:   "▶",
  \ "\\update" 	:   "⇝",
  \ "\\\"o"     :   "ö",
  \ "_a"        :   "ₐ",
  \ "_e"        :   "ₑ",
  \ "_h"        :   "ₕ",
  \ "_i"        :   "ᵢ",
  \ "_k"        :   "ₖ",
  \ "_l"        :   "ₗ",
  \ "_m"        :   "ₘ",
  \ "_n"        :   "ₙ",
  \ "_o"        :   "ₒ",
  \ "_p"        :   "ₚ",
  \ "_r"        :   "ᵣ",
  \ "_s"        :   "ₛ",
  \ "_t"        :   "ₜ",
  \ "_u"        :   "ᵤ",
  \ "_v"        :   "ᵥ",
  \ "_x"        :   "ₓ",
\ }
```


Alternatively, you can use snippets using [UltiSnips](https://github.com/SirVer/ultisnips).

Install it with your favorite plugin manager, and register a completion key in your configuration:
```
let g:UltiSnipsExpandTrigger="<c-l>"
```
To insert a unicode character, type its trigger word, such as `\forall` or `->`, and then press `<c-l>` while still in insert mode.

To register most common unicode characters, put [this file](vim_ultisnips) either at `~/.vim/UltiSnips/coq_unicode.snippets` or `~/.config/nvim/UltiSnips/coq_unicode.snippets`, depending on your preferred variant of Vim.
