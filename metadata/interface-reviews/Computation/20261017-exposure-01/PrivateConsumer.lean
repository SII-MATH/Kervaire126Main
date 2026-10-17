module
import PrivateDecl
#check visible
#check dependent
example : dependent.val = dependent.val := rfl
example : visible = 37 := rfl
example : dependent.val = 0 := rfl
