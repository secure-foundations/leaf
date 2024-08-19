# adjust for https://github.com/coq/coq/pull/13656
s/subgoal/goal/g
# merge with subsequent line for https://github.com/coq/coq/pull/14999
/[0-9]* focused goals\?$/{N;s/\n */ /;}
# locations in Fail added in https://github.com/coq/coq/pull/15174
/^File/d
# extra space removed in https://github.com/coq/coq/pull/16130
s/= $/=/
