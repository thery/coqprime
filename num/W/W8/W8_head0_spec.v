Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Open Local Scope w8_scope.
Require Import W8_lift.


Lemma Eq_not_Gt : Eq <> Gt.
Proof. intro H;discriminate H. Qed.

Lemma Eq_not_Lt : Eq <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma Lt_not_Gt : Lt <> Gt.
Proof. intro H;discriminate H. Qed.

Lemma Gt_not_Lt : Gt <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma w8_head0_spec : forall x, 0 < [|x|] -> w8_B/ 2 <= 2 ^ (Z_of_N (w8_head0 x)) * [|x|] < w8_B.
Proof
fun x =>
 match x as x return 0 < [|x|] -> w8_B/ 2 <= 2 ^ (Z_of_N (w8_head0 x)) * [|x|] < w8_B with
 | OOOOOOOO =>    fun (H:0 < [|OOOOOOOO|]) =>
    eq_ind Eq
      (fun ee : comparison =>
       match ee with
       | Eq => True
       | Lt => w8_B/ 2 <= 2 ^ (Z_of_N (w8_head0 OOOOOOOO)) * [|OOOOOOOO|] < w8_B
       | Gt => False
       end) I Lt H
 | OOOOOOOI =>    fun (H:0 < [|OOOOOOOI|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOOOOOIO =>    fun (H:0 < [|OOOOOOIO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOOOOOII =>    fun (H:0 < [|OOOOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOOIOO =>    fun (H:0 < [|OOOOOIOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOOOOIOI =>    fun (H:0 < [|OOOOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOOIIO =>    fun (H:0 < [|OOOOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOOIII =>    fun (H:0 < [|OOOOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIOOO =>    fun (H:0 < [|OOOOIOOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOOOIOOI =>    fun (H:0 < [|OOOOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIOIO =>    fun (H:0 < [|OOOOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIOII =>    fun (H:0 < [|OOOOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIIOO =>    fun (H:0 < [|OOOOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIIOI =>    fun (H:0 < [|OOOOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIIIO =>    fun (H:0 < [|OOOOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOOIIII =>    fun (H:0 < [|OOOOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOOOO =>    fun (H:0 < [|OOOIOOOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOOIOOOI =>    fun (H:0 < [|OOOIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOOIO =>    fun (H:0 < [|OOOIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOOII =>    fun (H:0 < [|OOOIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOIOO =>    fun (H:0 < [|OOOIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOIOI =>    fun (H:0 < [|OOOIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOIIO =>    fun (H:0 < [|OOOIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIOIII =>    fun (H:0 < [|OOOIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIOOO =>    fun (H:0 < [|OOOIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIOOI =>    fun (H:0 < [|OOOIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIOIO =>    fun (H:0 < [|OOOIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIOII =>    fun (H:0 < [|OOOIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIIOO =>    fun (H:0 < [|OOOIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIIOI =>    fun (H:0 < [|OOOIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIIIO =>    fun (H:0 < [|OOOIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOOIIIII =>    fun (H:0 < [|OOOIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOOOO =>    fun (H:0 < [|OOIOOOOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OOIOOOOI =>    fun (H:0 < [|OOIOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOOIO =>    fun (H:0 < [|OOIOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOOII =>    fun (H:0 < [|OOIOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOIOO =>    fun (H:0 < [|OOIOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOIOI =>    fun (H:0 < [|OOIOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOIIO =>    fun (H:0 < [|OOIOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOOIII =>    fun (H:0 < [|OOIOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIOOO =>    fun (H:0 < [|OOIOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIOOI =>    fun (H:0 < [|OOIOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIOIO =>    fun (H:0 < [|OOIOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIOII =>    fun (H:0 < [|OOIOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIIOO =>    fun (H:0 < [|OOIOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIIOI =>    fun (H:0 < [|OOIOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIIIO =>    fun (H:0 < [|OOIOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIOIIII =>    fun (H:0 < [|OOIOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOOOO =>    fun (H:0 < [|OOIIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOOOI =>    fun (H:0 < [|OOIIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOOIO =>    fun (H:0 < [|OOIIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOOII =>    fun (H:0 < [|OOIIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOIOO =>    fun (H:0 < [|OOIIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOIOI =>    fun (H:0 < [|OOIIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOIIO =>    fun (H:0 < [|OOIIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIOIII =>    fun (H:0 < [|OOIIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIOOO =>    fun (H:0 < [|OOIIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIOOI =>    fun (H:0 < [|OOIIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIOIO =>    fun (H:0 < [|OOIIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIOII =>    fun (H:0 < [|OOIIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIIOO =>    fun (H:0 < [|OOIIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIIOI =>    fun (H:0 < [|OOIIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIIIO =>    fun (H:0 < [|OOIIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OOIIIIII =>    fun (H:0 < [|OOIIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOOOO =>    fun (H:0 < [|OIOOOOOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | OIOOOOOI =>    fun (H:0 < [|OIOOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOOIO =>    fun (H:0 < [|OIOOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOOII =>    fun (H:0 < [|OIOOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOIOO =>    fun (H:0 < [|OIOOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOIOI =>    fun (H:0 < [|OIOOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOIIO =>    fun (H:0 < [|OIOOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOOIII =>    fun (H:0 < [|OIOOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIOOO =>    fun (H:0 < [|OIOOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIOOI =>    fun (H:0 < [|OIOOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIOIO =>    fun (H:0 < [|OIOOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIOII =>    fun (H:0 < [|OIOOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIIOO =>    fun (H:0 < [|OIOOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIIOI =>    fun (H:0 < [|OIOOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIIIO =>    fun (H:0 < [|OIOOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOOIIII =>    fun (H:0 < [|OIOOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOOOO =>    fun (H:0 < [|OIOIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOOOI =>    fun (H:0 < [|OIOIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOOIO =>    fun (H:0 < [|OIOIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOOII =>    fun (H:0 < [|OIOIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOIOO =>    fun (H:0 < [|OIOIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOIOI =>    fun (H:0 < [|OIOIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOIIO =>    fun (H:0 < [|OIOIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIOIII =>    fun (H:0 < [|OIOIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIOOO =>    fun (H:0 < [|OIOIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIOOI =>    fun (H:0 < [|OIOIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIOIO =>    fun (H:0 < [|OIOIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIOII =>    fun (H:0 < [|OIOIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIIOO =>    fun (H:0 < [|OIOIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIIOI =>    fun (H:0 < [|OIOIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIIIO =>    fun (H:0 < [|OIOIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIOIIIII =>    fun (H:0 < [|OIOIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOOOO =>    fun (H:0 < [|OIIOOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOOOI =>    fun (H:0 < [|OIIOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOOIO =>    fun (H:0 < [|OIIOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOOII =>    fun (H:0 < [|OIIOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOIOO =>    fun (H:0 < [|OIIOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOIOI =>    fun (H:0 < [|OIIOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOIIO =>    fun (H:0 < [|OIIOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOOIII =>    fun (H:0 < [|OIIOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIOOO =>    fun (H:0 < [|OIIOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIOOI =>    fun (H:0 < [|OIIOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIOIO =>    fun (H:0 < [|OIIOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIOII =>    fun (H:0 < [|OIIOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIIOO =>    fun (H:0 < [|OIIOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIIOI =>    fun (H:0 < [|OIIOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIIIO =>    fun (H:0 < [|OIIOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIOIIII =>    fun (H:0 < [|OIIOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOOOO =>    fun (H:0 < [|OIIIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOOOI =>    fun (H:0 < [|OIIIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOOIO =>    fun (H:0 < [|OIIIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOOII =>    fun (H:0 < [|OIIIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOIOO =>    fun (H:0 < [|OIIIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOIOI =>    fun (H:0 < [|OIIIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOIIO =>    fun (H:0 < [|OIIIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIOIII =>    fun (H:0 < [|OIIIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIOOO =>    fun (H:0 < [|OIIIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIOOI =>    fun (H:0 < [|OIIIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIOIO =>    fun (H:0 < [|OIIIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIOII =>    fun (H:0 < [|OIIIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIIOO =>    fun (H:0 < [|OIIIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIIOI =>    fun (H:0 < [|OIIIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIIIO =>    fun (H:0 < [|OIIIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | OIIIIIII =>    fun (H:0 < [|OIIIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOOOO =>    fun (H:0 < [|IOOOOOOO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | IOOOOOOI =>    fun (H:0 < [|IOOOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOOIO =>    fun (H:0 < [|IOOOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOOII =>    fun (H:0 < [|IOOOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOIOO =>    fun (H:0 < [|IOOOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOIOI =>    fun (H:0 < [|IOOOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOIIO =>    fun (H:0 < [|IOOOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOOIII =>    fun (H:0 < [|IOOOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIOOO =>    fun (H:0 < [|IOOOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIOOI =>    fun (H:0 < [|IOOOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIOIO =>    fun (H:0 < [|IOOOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIOII =>    fun (H:0 < [|IOOOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIIOO =>    fun (H:0 < [|IOOOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIIOI =>    fun (H:0 < [|IOOOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIIIO =>    fun (H:0 < [|IOOOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOOIIII =>    fun (H:0 < [|IOOOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOOOO =>    fun (H:0 < [|IOOIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOOOI =>    fun (H:0 < [|IOOIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOOIO =>    fun (H:0 < [|IOOIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOOII =>    fun (H:0 < [|IOOIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOIOO =>    fun (H:0 < [|IOOIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOIOI =>    fun (H:0 < [|IOOIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOIIO =>    fun (H:0 < [|IOOIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIOIII =>    fun (H:0 < [|IOOIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIOOO =>    fun (H:0 < [|IOOIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIOOI =>    fun (H:0 < [|IOOIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIOIO =>    fun (H:0 < [|IOOIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIOII =>    fun (H:0 < [|IOOIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIIOO =>    fun (H:0 < [|IOOIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIIOI =>    fun (H:0 < [|IOOIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIIIO =>    fun (H:0 < [|IOOIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOOIIIII =>    fun (H:0 < [|IOOIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOOOO =>    fun (H:0 < [|IOIOOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOOOI =>    fun (H:0 < [|IOIOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOOIO =>    fun (H:0 < [|IOIOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOOII =>    fun (H:0 < [|IOIOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOIOO =>    fun (H:0 < [|IOIOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOIOI =>    fun (H:0 < [|IOIOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOIIO =>    fun (H:0 < [|IOIOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOOIII =>    fun (H:0 < [|IOIOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIOOO =>    fun (H:0 < [|IOIOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIOOI =>    fun (H:0 < [|IOIOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIOIO =>    fun (H:0 < [|IOIOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIOII =>    fun (H:0 < [|IOIOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIIOO =>    fun (H:0 < [|IOIOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIIOI =>    fun (H:0 < [|IOIOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIIIO =>    fun (H:0 < [|IOIOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIOIIII =>    fun (H:0 < [|IOIOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOOOO =>    fun (H:0 < [|IOIIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOOOI =>    fun (H:0 < [|IOIIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOOIO =>    fun (H:0 < [|IOIIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOOII =>    fun (H:0 < [|IOIIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOIOO =>    fun (H:0 < [|IOIIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOIOI =>    fun (H:0 < [|IOIIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOIIO =>    fun (H:0 < [|IOIIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIOIII =>    fun (H:0 < [|IOIIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIOOO =>    fun (H:0 < [|IOIIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIOOI =>    fun (H:0 < [|IOIIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIOIO =>    fun (H:0 < [|IOIIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIOII =>    fun (H:0 < [|IOIIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIIOO =>    fun (H:0 < [|IOIIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIIOI =>    fun (H:0 < [|IOIIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIIIO =>    fun (H:0 < [|IOIIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IOIIIIII =>    fun (H:0 < [|IOIIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOOOO =>    fun (H:0 < [|IIOOOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOOOI =>    fun (H:0 < [|IIOOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOOIO =>    fun (H:0 < [|IIOOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOOII =>    fun (H:0 < [|IIOOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOIOO =>    fun (H:0 < [|IIOOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOIOI =>    fun (H:0 < [|IIOOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOIIO =>    fun (H:0 < [|IIOOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOOIII =>    fun (H:0 < [|IIOOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIOOO =>    fun (H:0 < [|IIOOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIOOI =>    fun (H:0 < [|IIOOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIOIO =>    fun (H:0 < [|IIOOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIOII =>    fun (H:0 < [|IIOOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIIOO =>    fun (H:0 < [|IIOOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIIOI =>    fun (H:0 < [|IIOOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIIIO =>    fun (H:0 < [|IIOOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOOIIII =>    fun (H:0 < [|IIOOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOOOO =>    fun (H:0 < [|IIOIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOOOI =>    fun (H:0 < [|IIOIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOOIO =>    fun (H:0 < [|IIOIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOOII =>    fun (H:0 < [|IIOIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOIOO =>    fun (H:0 < [|IIOIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOIOI =>    fun (H:0 < [|IIOIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOIIO =>    fun (H:0 < [|IIOIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIOIII =>    fun (H:0 < [|IIOIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIOOO =>    fun (H:0 < [|IIOIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIOOI =>    fun (H:0 < [|IIOIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIOIO =>    fun (H:0 < [|IIOIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIOII =>    fun (H:0 < [|IIOIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIIOO =>    fun (H:0 < [|IIOIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIIOI =>    fun (H:0 < [|IIOIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIIIO =>    fun (H:0 < [|IIOIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIOIIIII =>    fun (H:0 < [|IIOIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOOOO =>    fun (H:0 < [|IIIOOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOOOI =>    fun (H:0 < [|IIIOOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOOIO =>    fun (H:0 < [|IIIOOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOOII =>    fun (H:0 < [|IIIOOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOIOO =>    fun (H:0 < [|IIIOOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOIOI =>    fun (H:0 < [|IIIOOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOIIO =>    fun (H:0 < [|IIIOOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOOIII =>    fun (H:0 < [|IIIOOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIOOO =>    fun (H:0 < [|IIIOIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIOOI =>    fun (H:0 < [|IIIOIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIOIO =>    fun (H:0 < [|IIIOIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIOII =>    fun (H:0 < [|IIIOIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIIOO =>    fun (H:0 < [|IIIOIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIIOI =>    fun (H:0 < [|IIIOIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIIIO =>    fun (H:0 < [|IIIOIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIOIIII =>    fun (H:0 < [|IIIOIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOOOO =>    fun (H:0 < [|IIIIOOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOOOI =>    fun (H:0 < [|IIIIOOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOOIO =>    fun (H:0 < [|IIIIOOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOOII =>    fun (H:0 < [|IIIIOOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOIOO =>    fun (H:0 < [|IIIIOIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOIOI =>    fun (H:0 < [|IIIIOIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOIIO =>    fun (H:0 < [|IIIIOIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIOIII =>    fun (H:0 < [|IIIIOIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIOOO =>    fun (H:0 < [|IIIIIOOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIOOI =>    fun (H:0 < [|IIIIIOOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIOIO =>    fun (H:0 < [|IIIIIOIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIOII =>    fun (H:0 < [|IIIIIOII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIIOO =>    fun (H:0 < [|IIIIIIOO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIIOI =>    fun (H:0 < [|IIIIIIOI|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIIIO =>    fun (H:0 < [|IIIIIIIO|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 | IIIIIIII =>    fun (H:0 < [|IIIIIIII|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 end.

