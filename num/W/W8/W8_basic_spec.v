Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Open Local Scope w8_scope.



(* ** Proof that the basic functions are correct ** *)

Lemma w8_to_Z_spec : forall x, 0 <= [|x|] < w8_B.
Proof
fun x =>
 match x as x return 0 <= [|x|] < w8_B with
 | OOOOOOOO => conj (Zle_refl 0) (refl_equal Lt)
 | OOOOOOOI => conj (Zle_0_pos 1) (refl_equal Lt)
 | OOOOOOIO => conj (Zle_0_pos 2) (refl_equal Lt)
 | OOOOOOII => conj (Zle_0_pos 3) (refl_equal Lt)
 | OOOOOIOO => conj (Zle_0_pos 4) (refl_equal Lt)
 | OOOOOIOI => conj (Zle_0_pos 5) (refl_equal Lt)
 | OOOOOIIO => conj (Zle_0_pos 6) (refl_equal Lt)
 | OOOOOIII => conj (Zle_0_pos 7) (refl_equal Lt)
 | OOOOIOOO => conj (Zle_0_pos 8) (refl_equal Lt)
 | OOOOIOOI => conj (Zle_0_pos 9) (refl_equal Lt)
 | OOOOIOIO => conj (Zle_0_pos 10) (refl_equal Lt)
 | OOOOIOII => conj (Zle_0_pos 11) (refl_equal Lt)
 | OOOOIIOO => conj (Zle_0_pos 12) (refl_equal Lt)
 | OOOOIIOI => conj (Zle_0_pos 13) (refl_equal Lt)
 | OOOOIIIO => conj (Zle_0_pos 14) (refl_equal Lt)
 | OOOOIIII => conj (Zle_0_pos 15) (refl_equal Lt)
 | OOOIOOOO => conj (Zle_0_pos 16) (refl_equal Lt)
 | OOOIOOOI => conj (Zle_0_pos 17) (refl_equal Lt)
 | OOOIOOIO => conj (Zle_0_pos 18) (refl_equal Lt)
 | OOOIOOII => conj (Zle_0_pos 19) (refl_equal Lt)
 | OOOIOIOO => conj (Zle_0_pos 20) (refl_equal Lt)
 | OOOIOIOI => conj (Zle_0_pos 21) (refl_equal Lt)
 | OOOIOIIO => conj (Zle_0_pos 22) (refl_equal Lt)
 | OOOIOIII => conj (Zle_0_pos 23) (refl_equal Lt)
 | OOOIIOOO => conj (Zle_0_pos 24) (refl_equal Lt)
 | OOOIIOOI => conj (Zle_0_pos 25) (refl_equal Lt)
 | OOOIIOIO => conj (Zle_0_pos 26) (refl_equal Lt)
 | OOOIIOII => conj (Zle_0_pos 27) (refl_equal Lt)
 | OOOIIIOO => conj (Zle_0_pos 28) (refl_equal Lt)
 | OOOIIIOI => conj (Zle_0_pos 29) (refl_equal Lt)
 | OOOIIIIO => conj (Zle_0_pos 30) (refl_equal Lt)
 | OOOIIIII => conj (Zle_0_pos 31) (refl_equal Lt)
 | OOIOOOOO => conj (Zle_0_pos 32) (refl_equal Lt)
 | OOIOOOOI => conj (Zle_0_pos 33) (refl_equal Lt)
 | OOIOOOIO => conj (Zle_0_pos 34) (refl_equal Lt)
 | OOIOOOII => conj (Zle_0_pos 35) (refl_equal Lt)
 | OOIOOIOO => conj (Zle_0_pos 36) (refl_equal Lt)
 | OOIOOIOI => conj (Zle_0_pos 37) (refl_equal Lt)
 | OOIOOIIO => conj (Zle_0_pos 38) (refl_equal Lt)
 | OOIOOIII => conj (Zle_0_pos 39) (refl_equal Lt)
 | OOIOIOOO => conj (Zle_0_pos 40) (refl_equal Lt)
 | OOIOIOOI => conj (Zle_0_pos 41) (refl_equal Lt)
 | OOIOIOIO => conj (Zle_0_pos 42) (refl_equal Lt)
 | OOIOIOII => conj (Zle_0_pos 43) (refl_equal Lt)
 | OOIOIIOO => conj (Zle_0_pos 44) (refl_equal Lt)
 | OOIOIIOI => conj (Zle_0_pos 45) (refl_equal Lt)
 | OOIOIIIO => conj (Zle_0_pos 46) (refl_equal Lt)
 | OOIOIIII => conj (Zle_0_pos 47) (refl_equal Lt)
 | OOIIOOOO => conj (Zle_0_pos 48) (refl_equal Lt)
 | OOIIOOOI => conj (Zle_0_pos 49) (refl_equal Lt)
 | OOIIOOIO => conj (Zle_0_pos 50) (refl_equal Lt)
 | OOIIOOII => conj (Zle_0_pos 51) (refl_equal Lt)
 | OOIIOIOO => conj (Zle_0_pos 52) (refl_equal Lt)
 | OOIIOIOI => conj (Zle_0_pos 53) (refl_equal Lt)
 | OOIIOIIO => conj (Zle_0_pos 54) (refl_equal Lt)
 | OOIIOIII => conj (Zle_0_pos 55) (refl_equal Lt)
 | OOIIIOOO => conj (Zle_0_pos 56) (refl_equal Lt)
 | OOIIIOOI => conj (Zle_0_pos 57) (refl_equal Lt)
 | OOIIIOIO => conj (Zle_0_pos 58) (refl_equal Lt)
 | OOIIIOII => conj (Zle_0_pos 59) (refl_equal Lt)
 | OOIIIIOO => conj (Zle_0_pos 60) (refl_equal Lt)
 | OOIIIIOI => conj (Zle_0_pos 61) (refl_equal Lt)
 | OOIIIIIO => conj (Zle_0_pos 62) (refl_equal Lt)
 | OOIIIIII => conj (Zle_0_pos 63) (refl_equal Lt)
 | OIOOOOOO => conj (Zle_0_pos 64) (refl_equal Lt)
 | OIOOOOOI => conj (Zle_0_pos 65) (refl_equal Lt)
 | OIOOOOIO => conj (Zle_0_pos 66) (refl_equal Lt)
 | OIOOOOII => conj (Zle_0_pos 67) (refl_equal Lt)
 | OIOOOIOO => conj (Zle_0_pos 68) (refl_equal Lt)
 | OIOOOIOI => conj (Zle_0_pos 69) (refl_equal Lt)
 | OIOOOIIO => conj (Zle_0_pos 70) (refl_equal Lt)
 | OIOOOIII => conj (Zle_0_pos 71) (refl_equal Lt)
 | OIOOIOOO => conj (Zle_0_pos 72) (refl_equal Lt)
 | OIOOIOOI => conj (Zle_0_pos 73) (refl_equal Lt)
 | OIOOIOIO => conj (Zle_0_pos 74) (refl_equal Lt)
 | OIOOIOII => conj (Zle_0_pos 75) (refl_equal Lt)
 | OIOOIIOO => conj (Zle_0_pos 76) (refl_equal Lt)
 | OIOOIIOI => conj (Zle_0_pos 77) (refl_equal Lt)
 | OIOOIIIO => conj (Zle_0_pos 78) (refl_equal Lt)
 | OIOOIIII => conj (Zle_0_pos 79) (refl_equal Lt)
 | OIOIOOOO => conj (Zle_0_pos 80) (refl_equal Lt)
 | OIOIOOOI => conj (Zle_0_pos 81) (refl_equal Lt)
 | OIOIOOIO => conj (Zle_0_pos 82) (refl_equal Lt)
 | OIOIOOII => conj (Zle_0_pos 83) (refl_equal Lt)
 | OIOIOIOO => conj (Zle_0_pos 84) (refl_equal Lt)
 | OIOIOIOI => conj (Zle_0_pos 85) (refl_equal Lt)
 | OIOIOIIO => conj (Zle_0_pos 86) (refl_equal Lt)
 | OIOIOIII => conj (Zle_0_pos 87) (refl_equal Lt)
 | OIOIIOOO => conj (Zle_0_pos 88) (refl_equal Lt)
 | OIOIIOOI => conj (Zle_0_pos 89) (refl_equal Lt)
 | OIOIIOIO => conj (Zle_0_pos 90) (refl_equal Lt)
 | OIOIIOII => conj (Zle_0_pos 91) (refl_equal Lt)
 | OIOIIIOO => conj (Zle_0_pos 92) (refl_equal Lt)
 | OIOIIIOI => conj (Zle_0_pos 93) (refl_equal Lt)
 | OIOIIIIO => conj (Zle_0_pos 94) (refl_equal Lt)
 | OIOIIIII => conj (Zle_0_pos 95) (refl_equal Lt)
 | OIIOOOOO => conj (Zle_0_pos 96) (refl_equal Lt)
 | OIIOOOOI => conj (Zle_0_pos 97) (refl_equal Lt)
 | OIIOOOIO => conj (Zle_0_pos 98) (refl_equal Lt)
 | OIIOOOII => conj (Zle_0_pos 99) (refl_equal Lt)
 | OIIOOIOO => conj (Zle_0_pos 100) (refl_equal Lt)
 | OIIOOIOI => conj (Zle_0_pos 101) (refl_equal Lt)
 | OIIOOIIO => conj (Zle_0_pos 102) (refl_equal Lt)
 | OIIOOIII => conj (Zle_0_pos 103) (refl_equal Lt)
 | OIIOIOOO => conj (Zle_0_pos 104) (refl_equal Lt)
 | OIIOIOOI => conj (Zle_0_pos 105) (refl_equal Lt)
 | OIIOIOIO => conj (Zle_0_pos 106) (refl_equal Lt)
 | OIIOIOII => conj (Zle_0_pos 107) (refl_equal Lt)
 | OIIOIIOO => conj (Zle_0_pos 108) (refl_equal Lt)
 | OIIOIIOI => conj (Zle_0_pos 109) (refl_equal Lt)
 | OIIOIIIO => conj (Zle_0_pos 110) (refl_equal Lt)
 | OIIOIIII => conj (Zle_0_pos 111) (refl_equal Lt)
 | OIIIOOOO => conj (Zle_0_pos 112) (refl_equal Lt)
 | OIIIOOOI => conj (Zle_0_pos 113) (refl_equal Lt)
 | OIIIOOIO => conj (Zle_0_pos 114) (refl_equal Lt)
 | OIIIOOII => conj (Zle_0_pos 115) (refl_equal Lt)
 | OIIIOIOO => conj (Zle_0_pos 116) (refl_equal Lt)
 | OIIIOIOI => conj (Zle_0_pos 117) (refl_equal Lt)
 | OIIIOIIO => conj (Zle_0_pos 118) (refl_equal Lt)
 | OIIIOIII => conj (Zle_0_pos 119) (refl_equal Lt)
 | OIIIIOOO => conj (Zle_0_pos 120) (refl_equal Lt)
 | OIIIIOOI => conj (Zle_0_pos 121) (refl_equal Lt)
 | OIIIIOIO => conj (Zle_0_pos 122) (refl_equal Lt)
 | OIIIIOII => conj (Zle_0_pos 123) (refl_equal Lt)
 | OIIIIIOO => conj (Zle_0_pos 124) (refl_equal Lt)
 | OIIIIIOI => conj (Zle_0_pos 125) (refl_equal Lt)
 | OIIIIIIO => conj (Zle_0_pos 126) (refl_equal Lt)
 | OIIIIIII => conj (Zle_0_pos 127) (refl_equal Lt)
 | IOOOOOOO => conj (Zle_0_pos 128) (refl_equal Lt)
 | IOOOOOOI => conj (Zle_0_pos 129) (refl_equal Lt)
 | IOOOOOIO => conj (Zle_0_pos 130) (refl_equal Lt)
 | IOOOOOII => conj (Zle_0_pos 131) (refl_equal Lt)
 | IOOOOIOO => conj (Zle_0_pos 132) (refl_equal Lt)
 | IOOOOIOI => conj (Zle_0_pos 133) (refl_equal Lt)
 | IOOOOIIO => conj (Zle_0_pos 134) (refl_equal Lt)
 | IOOOOIII => conj (Zle_0_pos 135) (refl_equal Lt)
 | IOOOIOOO => conj (Zle_0_pos 136) (refl_equal Lt)
 | IOOOIOOI => conj (Zle_0_pos 137) (refl_equal Lt)
 | IOOOIOIO => conj (Zle_0_pos 138) (refl_equal Lt)
 | IOOOIOII => conj (Zle_0_pos 139) (refl_equal Lt)
 | IOOOIIOO => conj (Zle_0_pos 140) (refl_equal Lt)
 | IOOOIIOI => conj (Zle_0_pos 141) (refl_equal Lt)
 | IOOOIIIO => conj (Zle_0_pos 142) (refl_equal Lt)
 | IOOOIIII => conj (Zle_0_pos 143) (refl_equal Lt)
 | IOOIOOOO => conj (Zle_0_pos 144) (refl_equal Lt)
 | IOOIOOOI => conj (Zle_0_pos 145) (refl_equal Lt)
 | IOOIOOIO => conj (Zle_0_pos 146) (refl_equal Lt)
 | IOOIOOII => conj (Zle_0_pos 147) (refl_equal Lt)
 | IOOIOIOO => conj (Zle_0_pos 148) (refl_equal Lt)
 | IOOIOIOI => conj (Zle_0_pos 149) (refl_equal Lt)
 | IOOIOIIO => conj (Zle_0_pos 150) (refl_equal Lt)
 | IOOIOIII => conj (Zle_0_pos 151) (refl_equal Lt)
 | IOOIIOOO => conj (Zle_0_pos 152) (refl_equal Lt)
 | IOOIIOOI => conj (Zle_0_pos 153) (refl_equal Lt)
 | IOOIIOIO => conj (Zle_0_pos 154) (refl_equal Lt)
 | IOOIIOII => conj (Zle_0_pos 155) (refl_equal Lt)
 | IOOIIIOO => conj (Zle_0_pos 156) (refl_equal Lt)
 | IOOIIIOI => conj (Zle_0_pos 157) (refl_equal Lt)
 | IOOIIIIO => conj (Zle_0_pos 158) (refl_equal Lt)
 | IOOIIIII => conj (Zle_0_pos 159) (refl_equal Lt)
 | IOIOOOOO => conj (Zle_0_pos 160) (refl_equal Lt)
 | IOIOOOOI => conj (Zle_0_pos 161) (refl_equal Lt)
 | IOIOOOIO => conj (Zle_0_pos 162) (refl_equal Lt)
 | IOIOOOII => conj (Zle_0_pos 163) (refl_equal Lt)
 | IOIOOIOO => conj (Zle_0_pos 164) (refl_equal Lt)
 | IOIOOIOI => conj (Zle_0_pos 165) (refl_equal Lt)
 | IOIOOIIO => conj (Zle_0_pos 166) (refl_equal Lt)
 | IOIOOIII => conj (Zle_0_pos 167) (refl_equal Lt)
 | IOIOIOOO => conj (Zle_0_pos 168) (refl_equal Lt)
 | IOIOIOOI => conj (Zle_0_pos 169) (refl_equal Lt)
 | IOIOIOIO => conj (Zle_0_pos 170) (refl_equal Lt)
 | IOIOIOII => conj (Zle_0_pos 171) (refl_equal Lt)
 | IOIOIIOO => conj (Zle_0_pos 172) (refl_equal Lt)
 | IOIOIIOI => conj (Zle_0_pos 173) (refl_equal Lt)
 | IOIOIIIO => conj (Zle_0_pos 174) (refl_equal Lt)
 | IOIOIIII => conj (Zle_0_pos 175) (refl_equal Lt)
 | IOIIOOOO => conj (Zle_0_pos 176) (refl_equal Lt)
 | IOIIOOOI => conj (Zle_0_pos 177) (refl_equal Lt)
 | IOIIOOIO => conj (Zle_0_pos 178) (refl_equal Lt)
 | IOIIOOII => conj (Zle_0_pos 179) (refl_equal Lt)
 | IOIIOIOO => conj (Zle_0_pos 180) (refl_equal Lt)
 | IOIIOIOI => conj (Zle_0_pos 181) (refl_equal Lt)
 | IOIIOIIO => conj (Zle_0_pos 182) (refl_equal Lt)
 | IOIIOIII => conj (Zle_0_pos 183) (refl_equal Lt)
 | IOIIIOOO => conj (Zle_0_pos 184) (refl_equal Lt)
 | IOIIIOOI => conj (Zle_0_pos 185) (refl_equal Lt)
 | IOIIIOIO => conj (Zle_0_pos 186) (refl_equal Lt)
 | IOIIIOII => conj (Zle_0_pos 187) (refl_equal Lt)
 | IOIIIIOO => conj (Zle_0_pos 188) (refl_equal Lt)
 | IOIIIIOI => conj (Zle_0_pos 189) (refl_equal Lt)
 | IOIIIIIO => conj (Zle_0_pos 190) (refl_equal Lt)
 | IOIIIIII => conj (Zle_0_pos 191) (refl_equal Lt)
 | IIOOOOOO => conj (Zle_0_pos 192) (refl_equal Lt)
 | IIOOOOOI => conj (Zle_0_pos 193) (refl_equal Lt)
 | IIOOOOIO => conj (Zle_0_pos 194) (refl_equal Lt)
 | IIOOOOII => conj (Zle_0_pos 195) (refl_equal Lt)
 | IIOOOIOO => conj (Zle_0_pos 196) (refl_equal Lt)
 | IIOOOIOI => conj (Zle_0_pos 197) (refl_equal Lt)
 | IIOOOIIO => conj (Zle_0_pos 198) (refl_equal Lt)
 | IIOOOIII => conj (Zle_0_pos 199) (refl_equal Lt)
 | IIOOIOOO => conj (Zle_0_pos 200) (refl_equal Lt)
 | IIOOIOOI => conj (Zle_0_pos 201) (refl_equal Lt)
 | IIOOIOIO => conj (Zle_0_pos 202) (refl_equal Lt)
 | IIOOIOII => conj (Zle_0_pos 203) (refl_equal Lt)
 | IIOOIIOO => conj (Zle_0_pos 204) (refl_equal Lt)
 | IIOOIIOI => conj (Zle_0_pos 205) (refl_equal Lt)
 | IIOOIIIO => conj (Zle_0_pos 206) (refl_equal Lt)
 | IIOOIIII => conj (Zle_0_pos 207) (refl_equal Lt)
 | IIOIOOOO => conj (Zle_0_pos 208) (refl_equal Lt)
 | IIOIOOOI => conj (Zle_0_pos 209) (refl_equal Lt)
 | IIOIOOIO => conj (Zle_0_pos 210) (refl_equal Lt)
 | IIOIOOII => conj (Zle_0_pos 211) (refl_equal Lt)
 | IIOIOIOO => conj (Zle_0_pos 212) (refl_equal Lt)
 | IIOIOIOI => conj (Zle_0_pos 213) (refl_equal Lt)
 | IIOIOIIO => conj (Zle_0_pos 214) (refl_equal Lt)
 | IIOIOIII => conj (Zle_0_pos 215) (refl_equal Lt)
 | IIOIIOOO => conj (Zle_0_pos 216) (refl_equal Lt)
 | IIOIIOOI => conj (Zle_0_pos 217) (refl_equal Lt)
 | IIOIIOIO => conj (Zle_0_pos 218) (refl_equal Lt)
 | IIOIIOII => conj (Zle_0_pos 219) (refl_equal Lt)
 | IIOIIIOO => conj (Zle_0_pos 220) (refl_equal Lt)
 | IIOIIIOI => conj (Zle_0_pos 221) (refl_equal Lt)
 | IIOIIIIO => conj (Zle_0_pos 222) (refl_equal Lt)
 | IIOIIIII => conj (Zle_0_pos 223) (refl_equal Lt)
 | IIIOOOOO => conj (Zle_0_pos 224) (refl_equal Lt)
 | IIIOOOOI => conj (Zle_0_pos 225) (refl_equal Lt)
 | IIIOOOIO => conj (Zle_0_pos 226) (refl_equal Lt)
 | IIIOOOII => conj (Zle_0_pos 227) (refl_equal Lt)
 | IIIOOIOO => conj (Zle_0_pos 228) (refl_equal Lt)
 | IIIOOIOI => conj (Zle_0_pos 229) (refl_equal Lt)
 | IIIOOIIO => conj (Zle_0_pos 230) (refl_equal Lt)
 | IIIOOIII => conj (Zle_0_pos 231) (refl_equal Lt)
 | IIIOIOOO => conj (Zle_0_pos 232) (refl_equal Lt)
 | IIIOIOOI => conj (Zle_0_pos 233) (refl_equal Lt)
 | IIIOIOIO => conj (Zle_0_pos 234) (refl_equal Lt)
 | IIIOIOII => conj (Zle_0_pos 235) (refl_equal Lt)
 | IIIOIIOO => conj (Zle_0_pos 236) (refl_equal Lt)
 | IIIOIIOI => conj (Zle_0_pos 237) (refl_equal Lt)
 | IIIOIIIO => conj (Zle_0_pos 238) (refl_equal Lt)
 | IIIOIIII => conj (Zle_0_pos 239) (refl_equal Lt)
 | IIIIOOOO => conj (Zle_0_pos 240) (refl_equal Lt)
 | IIIIOOOI => conj (Zle_0_pos 241) (refl_equal Lt)
 | IIIIOOIO => conj (Zle_0_pos 242) (refl_equal Lt)
 | IIIIOOII => conj (Zle_0_pos 243) (refl_equal Lt)
 | IIIIOIOO => conj (Zle_0_pos 244) (refl_equal Lt)
 | IIIIOIOI => conj (Zle_0_pos 245) (refl_equal Lt)
 | IIIIOIIO => conj (Zle_0_pos 246) (refl_equal Lt)
 | IIIIOIII => conj (Zle_0_pos 247) (refl_equal Lt)
 | IIIIIOOO => conj (Zle_0_pos 248) (refl_equal Lt)
 | IIIIIOOI => conj (Zle_0_pos 249) (refl_equal Lt)
 | IIIIIOIO => conj (Zle_0_pos 250) (refl_equal Lt)
 | IIIIIOII => conj (Zle_0_pos 251) (refl_equal Lt)
 | IIIIIIOO => conj (Zle_0_pos 252) (refl_equal Lt)
 | IIIIIIOI => conj (Zle_0_pos 253) (refl_equal Lt)
 | IIIIIIIO => conj (Zle_0_pos 254) (refl_equal Lt)
 | IIIIIIII => conj (Zle_0_pos 255) (refl_equal Lt)
end.

Lemma w8_of_pos_spec : forall p, Zpos p = (Z_of_N (fst (w8_of_pos p)))*w8_B + [|snd (w8_of_pos p)|].
Proof
fun p0 =>
 eq_ind_r (fun z : Z => Zpos p0 = z + [|snd (w8_of_pos p0)|])
 match p0 as p0 return Zpos p0 = w8_B*(Z_of_N (fst (w8_of_pos p0))) + [|snd (w8_of_pos p0)|] with
 | xH => refl_equal (Zpos xH)
 | xO p1 =>
    match p1 as p1 return Zpos (xO p1) = w8_B*(Z_of_N (fst (w8_of_pos (xO p1)))) + [|snd (w8_of_pos (xO p1))|] with
    | xH => refl_equal (Zpos (xO xH))
    | xO p2 =>
       match p2 as p2 return Zpos (xO (xO p2)) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO p2))))) + [|snd (w8_of_pos (xO (xO p2)))|] with
       | xH => refl_equal (Zpos (xO (xO xH)))
       | xO p3 =>
          match p3 as p3 return Zpos (xO (xO (xO p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO p3)))))) + [|snd (w8_of_pos (xO (xO (xO p3))))|] with
          | xH => refl_equal (Zpos (xO (xO (xO xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xO (xO (xO (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO p4))))))) + [|snd (w8_of_pos (xO (xO (xO (xO p4)))))|] with
             | xH => refl_equal (Zpos (xO (xO (xO (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xO (xO (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO p5)))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xO (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xO (xO (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI p5)))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xO (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xO (xO (xO (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI p4))))))) + [|snd (w8_of_pos (xO (xO (xO (xI p4)))))|] with
             | xH => refl_equal (Zpos (xO (xO (xO (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xO (xO (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO p5)))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xO (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xO (xO (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI p5)))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xO (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xO (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xO (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xO (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xO (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xO (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       | xI p3 =>
          match p3 as p3 return Zpos (xO (xO (xI p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI p3)))))) + [|snd (w8_of_pos (xO (xO (xI p3))))|] with
          | xH => refl_equal (Zpos (xO (xO (xI xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xO (xO (xI (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO p4))))))) + [|snd (w8_of_pos (xO (xO (xI (xO p4)))))|] with
             | xH => refl_equal (Zpos (xO (xO (xI (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xO (xI (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO p5)))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xI (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xO (xI (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI p5)))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xI (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xO (xO (xI (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI p4))))))) + [|snd (w8_of_pos (xO (xO (xI (xI p4)))))|] with
             | xH => refl_equal (Zpos (xO (xO (xI (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xO (xI (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO p5)))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xI (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xO (xI (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI p5)))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xO (xI (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xO (xI (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xO (xI (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xO (xI (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xO (xI (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xO (xI (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       end
    | xI p2 =>
       match p2 as p2 return Zpos (xO (xI p2)) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI p2))))) + [|snd (w8_of_pos (xO (xI p2)))|] with
       | xH => refl_equal (Zpos (xO (xI xH)))
       | xO p3 =>
          match p3 as p3 return Zpos (xO (xI (xO p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO p3)))))) + [|snd (w8_of_pos (xO (xI (xO p3))))|] with
          | xH => refl_equal (Zpos (xO (xI (xO xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xO (xI (xO (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO p4))))))) + [|snd (w8_of_pos (xO (xI (xO (xO p4)))))|] with
             | xH => refl_equal (Zpos (xO (xI (xO (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xI (xO (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO p5)))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xO (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xI (xO (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI p5)))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xO (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xO (xI (xO (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI p4))))))) + [|snd (w8_of_pos (xO (xI (xO (xI p4)))))|] with
             | xH => refl_equal (Zpos (xO (xI (xO (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xI (xO (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO p5)))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xO (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xI (xO (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI p5)))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xO (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xO (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xO (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xO (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xO (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xO (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       | xI p3 =>
          match p3 as p3 return Zpos (xO (xI (xI p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI p3)))))) + [|snd (w8_of_pos (xO (xI (xI p3))))|] with
          | xH => refl_equal (Zpos (xO (xI (xI xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xO (xI (xI (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO p4))))))) + [|snd (w8_of_pos (xO (xI (xI (xO p4)))))|] with
             | xH => refl_equal (Zpos (xO (xI (xI (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xI (xI (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO p5)))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xI (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xI (xI (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI p5)))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xI (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xO (xI (xI (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI p4))))))) + [|snd (w8_of_pos (xO (xI (xI (xI p4)))))|] with
             | xH => refl_equal (Zpos (xO (xI (xI (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xO (xI (xI (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO p5)))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xI (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xO (xI (xI (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI p5)))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xO (xI (xI (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xO (xI (xI (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xO (xI (xI (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xO (xI (xI (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xO (xI (xI (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xO (xI (xI (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       end
    end
 | xI p1 =>
    match p1 as p1 return Zpos (xI p1) = w8_B*(Z_of_N (fst (w8_of_pos (xI p1)))) + [|snd (w8_of_pos (xI p1))|] with
    | xH => refl_equal (Zpos (xI xH))
    | xO p2 =>
       match p2 as p2 return Zpos (xI (xO p2)) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO p2))))) + [|snd (w8_of_pos (xI (xO p2)))|] with
       | xH => refl_equal (Zpos (xI (xO xH)))
       | xO p3 =>
          match p3 as p3 return Zpos (xI (xO (xO p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO p3)))))) + [|snd (w8_of_pos (xI (xO (xO p3))))|] with
          | xH => refl_equal (Zpos (xI (xO (xO xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xI (xO (xO (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO p4))))))) + [|snd (w8_of_pos (xI (xO (xO (xO p4)))))|] with
             | xH => refl_equal (Zpos (xI (xO (xO (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xO (xO (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO p5)))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xO (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xO (xO (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI p5)))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xO (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xI (xO (xO (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI p4))))))) + [|snd (w8_of_pos (xI (xO (xO (xI p4)))))|] with
             | xH => refl_equal (Zpos (xI (xO (xO (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xO (xO (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO p5)))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xO (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xO (xO (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI p5)))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xO (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xO (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xO (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xO (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xO (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xO (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       | xI p3 =>
          match p3 as p3 return Zpos (xI (xO (xI p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI p3)))))) + [|snd (w8_of_pos (xI (xO (xI p3))))|] with
          | xH => refl_equal (Zpos (xI (xO (xI xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xI (xO (xI (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO p4))))))) + [|snd (w8_of_pos (xI (xO (xI (xO p4)))))|] with
             | xH => refl_equal (Zpos (xI (xO (xI (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xO (xI (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO p5)))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xI (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xO (xI (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI p5)))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xI (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xI (xO (xI (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI p4))))))) + [|snd (w8_of_pos (xI (xO (xI (xI p4)))))|] with
             | xH => refl_equal (Zpos (xI (xO (xI (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xO (xI (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO p5)))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xI (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xO (xI (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI p5)))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xO (xI (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xO (xI (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xO (xI (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xO (xI (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xO (xI (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xO (xI (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       end
    | xI p2 =>
       match p2 as p2 return Zpos (xI (xI p2)) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI p2))))) + [|snd (w8_of_pos (xI (xI p2)))|] with
       | xH => refl_equal (Zpos (xI (xI xH)))
       | xO p3 =>
          match p3 as p3 return Zpos (xI (xI (xO p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO p3)))))) + [|snd (w8_of_pos (xI (xI (xO p3))))|] with
          | xH => refl_equal (Zpos (xI (xI (xO xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xI (xI (xO (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO p4))))))) + [|snd (w8_of_pos (xI (xI (xO (xO p4)))))|] with
             | xH => refl_equal (Zpos (xI (xI (xO (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xI (xO (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO p5)))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xO (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xI (xO (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI p5)))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xO (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xI (xI (xO (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI p4))))))) + [|snd (w8_of_pos (xI (xI (xO (xI p4)))))|] with
             | xH => refl_equal (Zpos (xI (xI (xO (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xI (xO (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO p5)))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xO (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xI (xO (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI p5)))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xO (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xO (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xO (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xO (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xO (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xO (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       | xI p3 =>
          match p3 as p3 return Zpos (xI (xI (xI p3))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI p3)))))) + [|snd (w8_of_pos (xI (xI (xI p3))))|] with
          | xH => refl_equal (Zpos (xI (xI (xI xH))))
          | xO p4 =>
             match p4 as p4 return Zpos (xI (xI (xI (xO p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO p4))))))) + [|snd (w8_of_pos (xI (xI (xI (xO p4)))))|] with
             | xH => refl_equal (Zpos (xI (xI (xI (xO xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xI (xI (xO (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO p5)))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xI (xO (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xO (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xO (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xI (xI (xO (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI p5)))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xI (xO (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xO (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xO (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xO (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xO (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xO (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xO (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          | xI p4 =>
             match p4 as p4 return Zpos (xI (xI (xI (xI p4)))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI p4))))))) + [|snd (w8_of_pos (xI (xI (xI (xI p4)))))|] with
             | xH => refl_equal (Zpos (xI (xI (xI (xI xH)))))
             | xO p5 =>
                match p5 as p5 return Zpos (xI (xI (xI (xI (xO p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO p5)))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xI (xI (xO xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xI (xO (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xO (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xO (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xI (xO (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xO (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xO (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xO (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xO (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xO (xI (xI (xI p8)))))))))
                      end
                   end
                end
             | xI p5 =>
                match p5 as p5 return Zpos (xI (xI (xI (xI (xI p5))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI p5)))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI p5))))))|] with
                | xH => refl_equal (Zpos (xI (xI (xI (xI (xI xH))))))
                | xO p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xI (xI (xO p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xO p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xO p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xO xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xI (xO (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xO (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xO (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xI (xO (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xO (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xO (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xO (xI (xI p8)))))))))
                      end
                   end
                | xI p6 =>
                   match p6 as p6 return Zpos (xI (xI (xI (xI (xI (xI p6)))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xI p6))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xI p6)))))))|] with
                   | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xI xH)))))))
                   | xO p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xI (xI (xO p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xI (xO p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xI (xO p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xO xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xO (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xO (xI p8)))))))))
                      end
                   | xI p7 =>
                      match p7 as p7 return Zpos (xI (xI (xI (xI (xI (xI (xI p7))))))) = w8_B*(Z_of_N (fst (w8_of_pos (xI (xI (xI (xI (xI (xI (xI p7)))))))))) + [|snd (w8_of_pos (xI (xI (xI (xI (xI (xI (xI p7))))))))|] with
                      | xH => refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))
                      | xO p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xI (xO p8)))))))))
                      | xI p8 =>
                        refl_equal (Zpos (xI (xI (xI (xI (xI (xI (xI (xI p8)))))))))
                      end
                   end
                end
             end
          end
       end
    end
 end (Zmult_comm (Z_of_N (fst (w8_of_pos p0))) w8_B).

Lemma w8_0_spec : [|OOOOOOOO|] = 0.
Proof
(refl_equal 0).

Lemma w8_1_spec : [|OOOOOOOI|] = 1.
Proof
(refl_equal 1).

Lemma w8_Bm1_spec : [|IIIIIIII|] = w8_B - 1.
Proof
(refl_equal 255).

Lemma w8_WW_spec : forall h l, [||w8_WW h l||] = [|h|] * w8_B + [|l|].
Proof
fun h l =>
 match h as h return [||w8_WW h l||] = [|h|] * w8_B + [|l|] with
 | OOOOOOOO => 
    match l as l return [||w8_WW OOOOOOOO l||] = [|OOOOOOOO|] * w8_B + [|l|] with
    | OOOOOOOO => refl_equal 0
    | OOOOOOOI => refl_equal 1
    | OOOOOOIO => refl_equal 2
    | OOOOOOII => refl_equal 3
    | OOOOOIOO => refl_equal 4
    | OOOOOIOI => refl_equal 5
    | OOOOOIIO => refl_equal 6
    | OOOOOIII => refl_equal 7
    | OOOOIOOO => refl_equal 8
    | OOOOIOOI => refl_equal 9
    | OOOOIOIO => refl_equal 10
    | OOOOIOII => refl_equal 11
    | OOOOIIOO => refl_equal 12
    | OOOOIIOI => refl_equal 13
    | OOOOIIIO => refl_equal 14
    | OOOOIIII => refl_equal 15
    | OOOIOOOO => refl_equal 16
    | OOOIOOOI => refl_equal 17
    | OOOIOOIO => refl_equal 18
    | OOOIOOII => refl_equal 19
    | OOOIOIOO => refl_equal 20
    | OOOIOIOI => refl_equal 21
    | OOOIOIIO => refl_equal 22
    | OOOIOIII => refl_equal 23
    | OOOIIOOO => refl_equal 24
    | OOOIIOOI => refl_equal 25
    | OOOIIOIO => refl_equal 26
    | OOOIIOII => refl_equal 27
    | OOOIIIOO => refl_equal 28
    | OOOIIIOI => refl_equal 29
    | OOOIIIIO => refl_equal 30
    | OOOIIIII => refl_equal 31
    | OOIOOOOO => refl_equal 32
    | OOIOOOOI => refl_equal 33
    | OOIOOOIO => refl_equal 34
    | OOIOOOII => refl_equal 35
    | OOIOOIOO => refl_equal 36
    | OOIOOIOI => refl_equal 37
    | OOIOOIIO => refl_equal 38
    | OOIOOIII => refl_equal 39
    | OOIOIOOO => refl_equal 40
    | OOIOIOOI => refl_equal 41
    | OOIOIOIO => refl_equal 42
    | OOIOIOII => refl_equal 43
    | OOIOIIOO => refl_equal 44
    | OOIOIIOI => refl_equal 45
    | OOIOIIIO => refl_equal 46
    | OOIOIIII => refl_equal 47
    | OOIIOOOO => refl_equal 48
    | OOIIOOOI => refl_equal 49
    | OOIIOOIO => refl_equal 50
    | OOIIOOII => refl_equal 51
    | OOIIOIOO => refl_equal 52
    | OOIIOIOI => refl_equal 53
    | OOIIOIIO => refl_equal 54
    | OOIIOIII => refl_equal 55
    | OOIIIOOO => refl_equal 56
    | OOIIIOOI => refl_equal 57
    | OOIIIOIO => refl_equal 58
    | OOIIIOII => refl_equal 59
    | OOIIIIOO => refl_equal 60
    | OOIIIIOI => refl_equal 61
    | OOIIIIIO => refl_equal 62
    | OOIIIIII => refl_equal 63
    | OIOOOOOO => refl_equal 64
    | OIOOOOOI => refl_equal 65
    | OIOOOOIO => refl_equal 66
    | OIOOOOII => refl_equal 67
    | OIOOOIOO => refl_equal 68
    | OIOOOIOI => refl_equal 69
    | OIOOOIIO => refl_equal 70
    | OIOOOIII => refl_equal 71
    | OIOOIOOO => refl_equal 72
    | OIOOIOOI => refl_equal 73
    | OIOOIOIO => refl_equal 74
    | OIOOIOII => refl_equal 75
    | OIOOIIOO => refl_equal 76
    | OIOOIIOI => refl_equal 77
    | OIOOIIIO => refl_equal 78
    | OIOOIIII => refl_equal 79
    | OIOIOOOO => refl_equal 80
    | OIOIOOOI => refl_equal 81
    | OIOIOOIO => refl_equal 82
    | OIOIOOII => refl_equal 83
    | OIOIOIOO => refl_equal 84
    | OIOIOIOI => refl_equal 85
    | OIOIOIIO => refl_equal 86
    | OIOIOIII => refl_equal 87
    | OIOIIOOO => refl_equal 88
    | OIOIIOOI => refl_equal 89
    | OIOIIOIO => refl_equal 90
    | OIOIIOII => refl_equal 91
    | OIOIIIOO => refl_equal 92
    | OIOIIIOI => refl_equal 93
    | OIOIIIIO => refl_equal 94
    | OIOIIIII => refl_equal 95
    | OIIOOOOO => refl_equal 96
    | OIIOOOOI => refl_equal 97
    | OIIOOOIO => refl_equal 98
    | OIIOOOII => refl_equal 99
    | OIIOOIOO => refl_equal 100
    | OIIOOIOI => refl_equal 101
    | OIIOOIIO => refl_equal 102
    | OIIOOIII => refl_equal 103
    | OIIOIOOO => refl_equal 104
    | OIIOIOOI => refl_equal 105
    | OIIOIOIO => refl_equal 106
    | OIIOIOII => refl_equal 107
    | OIIOIIOO => refl_equal 108
    | OIIOIIOI => refl_equal 109
    | OIIOIIIO => refl_equal 110
    | OIIOIIII => refl_equal 111
    | OIIIOOOO => refl_equal 112
    | OIIIOOOI => refl_equal 113
    | OIIIOOIO => refl_equal 114
    | OIIIOOII => refl_equal 115
    | OIIIOIOO => refl_equal 116
    | OIIIOIOI => refl_equal 117
    | OIIIOIIO => refl_equal 118
    | OIIIOIII => refl_equal 119
    | OIIIIOOO => refl_equal 120
    | OIIIIOOI => refl_equal 121
    | OIIIIOIO => refl_equal 122
    | OIIIIOII => refl_equal 123
    | OIIIIIOO => refl_equal 124
    | OIIIIIOI => refl_equal 125
    | OIIIIIIO => refl_equal 126
    | OIIIIIII => refl_equal 127
    | IOOOOOOO => refl_equal 128
    | IOOOOOOI => refl_equal 129
    | IOOOOOIO => refl_equal 130
    | IOOOOOII => refl_equal 131
    | IOOOOIOO => refl_equal 132
    | IOOOOIOI => refl_equal 133
    | IOOOOIIO => refl_equal 134
    | IOOOOIII => refl_equal 135
    | IOOOIOOO => refl_equal 136
    | IOOOIOOI => refl_equal 137
    | IOOOIOIO => refl_equal 138
    | IOOOIOII => refl_equal 139
    | IOOOIIOO => refl_equal 140
    | IOOOIIOI => refl_equal 141
    | IOOOIIIO => refl_equal 142
    | IOOOIIII => refl_equal 143
    | IOOIOOOO => refl_equal 144
    | IOOIOOOI => refl_equal 145
    | IOOIOOIO => refl_equal 146
    | IOOIOOII => refl_equal 147
    | IOOIOIOO => refl_equal 148
    | IOOIOIOI => refl_equal 149
    | IOOIOIIO => refl_equal 150
    | IOOIOIII => refl_equal 151
    | IOOIIOOO => refl_equal 152
    | IOOIIOOI => refl_equal 153
    | IOOIIOIO => refl_equal 154
    | IOOIIOII => refl_equal 155
    | IOOIIIOO => refl_equal 156
    | IOOIIIOI => refl_equal 157
    | IOOIIIIO => refl_equal 158
    | IOOIIIII => refl_equal 159
    | IOIOOOOO => refl_equal 160
    | IOIOOOOI => refl_equal 161
    | IOIOOOIO => refl_equal 162
    | IOIOOOII => refl_equal 163
    | IOIOOIOO => refl_equal 164
    | IOIOOIOI => refl_equal 165
    | IOIOOIIO => refl_equal 166
    | IOIOOIII => refl_equal 167
    | IOIOIOOO => refl_equal 168
    | IOIOIOOI => refl_equal 169
    | IOIOIOIO => refl_equal 170
    | IOIOIOII => refl_equal 171
    | IOIOIIOO => refl_equal 172
    | IOIOIIOI => refl_equal 173
    | IOIOIIIO => refl_equal 174
    | IOIOIIII => refl_equal 175
    | IOIIOOOO => refl_equal 176
    | IOIIOOOI => refl_equal 177
    | IOIIOOIO => refl_equal 178
    | IOIIOOII => refl_equal 179
    | IOIIOIOO => refl_equal 180
    | IOIIOIOI => refl_equal 181
    | IOIIOIIO => refl_equal 182
    | IOIIOIII => refl_equal 183
    | IOIIIOOO => refl_equal 184
    | IOIIIOOI => refl_equal 185
    | IOIIIOIO => refl_equal 186
    | IOIIIOII => refl_equal 187
    | IOIIIIOO => refl_equal 188
    | IOIIIIOI => refl_equal 189
    | IOIIIIIO => refl_equal 190
    | IOIIIIII => refl_equal 191
    | IIOOOOOO => refl_equal 192
    | IIOOOOOI => refl_equal 193
    | IIOOOOIO => refl_equal 194
    | IIOOOOII => refl_equal 195
    | IIOOOIOO => refl_equal 196
    | IIOOOIOI => refl_equal 197
    | IIOOOIIO => refl_equal 198
    | IIOOOIII => refl_equal 199
    | IIOOIOOO => refl_equal 200
    | IIOOIOOI => refl_equal 201
    | IIOOIOIO => refl_equal 202
    | IIOOIOII => refl_equal 203
    | IIOOIIOO => refl_equal 204
    | IIOOIIOI => refl_equal 205
    | IIOOIIIO => refl_equal 206
    | IIOOIIII => refl_equal 207
    | IIOIOOOO => refl_equal 208
    | IIOIOOOI => refl_equal 209
    | IIOIOOIO => refl_equal 210
    | IIOIOOII => refl_equal 211
    | IIOIOIOO => refl_equal 212
    | IIOIOIOI => refl_equal 213
    | IIOIOIIO => refl_equal 214
    | IIOIOIII => refl_equal 215
    | IIOIIOOO => refl_equal 216
    | IIOIIOOI => refl_equal 217
    | IIOIIOIO => refl_equal 218
    | IIOIIOII => refl_equal 219
    | IIOIIIOO => refl_equal 220
    | IIOIIIOI => refl_equal 221
    | IIOIIIIO => refl_equal 222
    | IIOIIIII => refl_equal 223
    | IIIOOOOO => refl_equal 224
    | IIIOOOOI => refl_equal 225
    | IIIOOOIO => refl_equal 226
    | IIIOOOII => refl_equal 227
    | IIIOOIOO => refl_equal 228
    | IIIOOIOI => refl_equal 229
    | IIIOOIIO => refl_equal 230
    | IIIOOIII => refl_equal 231
    | IIIOIOOO => refl_equal 232
    | IIIOIOOI => refl_equal 233
    | IIIOIOIO => refl_equal 234
    | IIIOIOII => refl_equal 235
    | IIIOIIOO => refl_equal 236
    | IIIOIIOI => refl_equal 237
    | IIIOIIIO => refl_equal 238
    | IIIOIIII => refl_equal 239
    | IIIIOOOO => refl_equal 240
    | IIIIOOOI => refl_equal 241
    | IIIIOOIO => refl_equal 242
    | IIIIOOII => refl_equal 243
    | IIIIOIOO => refl_equal 244
    | IIIIOIOI => refl_equal 245
    | IIIIOIIO => refl_equal 246
    | IIIIOIII => refl_equal 247
    | IIIIIOOO => refl_equal 248
    | IIIIIOOI => refl_equal 249
    | IIIIIOIO => refl_equal 250
    | IIIIIOII => refl_equal 251
    | IIIIIIOO => refl_equal 252
    | IIIIIIOI => refl_equal 253
    | IIIIIIIO => refl_equal 254
    | IIIIIIII => refl_equal 255
    end
 | OOOOOOOI => refl_equal ([||w8_WW OOOOOOOI l||])
 | OOOOOOIO => refl_equal ([||w8_WW OOOOOOIO l||])
 | OOOOOOII => refl_equal ([||w8_WW OOOOOOII l||])
 | OOOOOIOO => refl_equal ([||w8_WW OOOOOIOO l||])
 | OOOOOIOI => refl_equal ([||w8_WW OOOOOIOI l||])
 | OOOOOIIO => refl_equal ([||w8_WW OOOOOIIO l||])
 | OOOOOIII => refl_equal ([||w8_WW OOOOOIII l||])
 | OOOOIOOO => refl_equal ([||w8_WW OOOOIOOO l||])
 | OOOOIOOI => refl_equal ([||w8_WW OOOOIOOI l||])
 | OOOOIOIO => refl_equal ([||w8_WW OOOOIOIO l||])
 | OOOOIOII => refl_equal ([||w8_WW OOOOIOII l||])
 | OOOOIIOO => refl_equal ([||w8_WW OOOOIIOO l||])
 | OOOOIIOI => refl_equal ([||w8_WW OOOOIIOI l||])
 | OOOOIIIO => refl_equal ([||w8_WW OOOOIIIO l||])
 | OOOOIIII => refl_equal ([||w8_WW OOOOIIII l||])
 | OOOIOOOO => refl_equal ([||w8_WW OOOIOOOO l||])
 | OOOIOOOI => refl_equal ([||w8_WW OOOIOOOI l||])
 | OOOIOOIO => refl_equal ([||w8_WW OOOIOOIO l||])
 | OOOIOOII => refl_equal ([||w8_WW OOOIOOII l||])
 | OOOIOIOO => refl_equal ([||w8_WW OOOIOIOO l||])
 | OOOIOIOI => refl_equal ([||w8_WW OOOIOIOI l||])
 | OOOIOIIO => refl_equal ([||w8_WW OOOIOIIO l||])
 | OOOIOIII => refl_equal ([||w8_WW OOOIOIII l||])
 | OOOIIOOO => refl_equal ([||w8_WW OOOIIOOO l||])
 | OOOIIOOI => refl_equal ([||w8_WW OOOIIOOI l||])
 | OOOIIOIO => refl_equal ([||w8_WW OOOIIOIO l||])
 | OOOIIOII => refl_equal ([||w8_WW OOOIIOII l||])
 | OOOIIIOO => refl_equal ([||w8_WW OOOIIIOO l||])
 | OOOIIIOI => refl_equal ([||w8_WW OOOIIIOI l||])
 | OOOIIIIO => refl_equal ([||w8_WW OOOIIIIO l||])
 | OOOIIIII => refl_equal ([||w8_WW OOOIIIII l||])
 | OOIOOOOO => refl_equal ([||w8_WW OOIOOOOO l||])
 | OOIOOOOI => refl_equal ([||w8_WW OOIOOOOI l||])
 | OOIOOOIO => refl_equal ([||w8_WW OOIOOOIO l||])
 | OOIOOOII => refl_equal ([||w8_WW OOIOOOII l||])
 | OOIOOIOO => refl_equal ([||w8_WW OOIOOIOO l||])
 | OOIOOIOI => refl_equal ([||w8_WW OOIOOIOI l||])
 | OOIOOIIO => refl_equal ([||w8_WW OOIOOIIO l||])
 | OOIOOIII => refl_equal ([||w8_WW OOIOOIII l||])
 | OOIOIOOO => refl_equal ([||w8_WW OOIOIOOO l||])
 | OOIOIOOI => refl_equal ([||w8_WW OOIOIOOI l||])
 | OOIOIOIO => refl_equal ([||w8_WW OOIOIOIO l||])
 | OOIOIOII => refl_equal ([||w8_WW OOIOIOII l||])
 | OOIOIIOO => refl_equal ([||w8_WW OOIOIIOO l||])
 | OOIOIIOI => refl_equal ([||w8_WW OOIOIIOI l||])
 | OOIOIIIO => refl_equal ([||w8_WW OOIOIIIO l||])
 | OOIOIIII => refl_equal ([||w8_WW OOIOIIII l||])
 | OOIIOOOO => refl_equal ([||w8_WW OOIIOOOO l||])
 | OOIIOOOI => refl_equal ([||w8_WW OOIIOOOI l||])
 | OOIIOOIO => refl_equal ([||w8_WW OOIIOOIO l||])
 | OOIIOOII => refl_equal ([||w8_WW OOIIOOII l||])
 | OOIIOIOO => refl_equal ([||w8_WW OOIIOIOO l||])
 | OOIIOIOI => refl_equal ([||w8_WW OOIIOIOI l||])
 | OOIIOIIO => refl_equal ([||w8_WW OOIIOIIO l||])
 | OOIIOIII => refl_equal ([||w8_WW OOIIOIII l||])
 | OOIIIOOO => refl_equal ([||w8_WW OOIIIOOO l||])
 | OOIIIOOI => refl_equal ([||w8_WW OOIIIOOI l||])
 | OOIIIOIO => refl_equal ([||w8_WW OOIIIOIO l||])
 | OOIIIOII => refl_equal ([||w8_WW OOIIIOII l||])
 | OOIIIIOO => refl_equal ([||w8_WW OOIIIIOO l||])
 | OOIIIIOI => refl_equal ([||w8_WW OOIIIIOI l||])
 | OOIIIIIO => refl_equal ([||w8_WW OOIIIIIO l||])
 | OOIIIIII => refl_equal ([||w8_WW OOIIIIII l||])
 | OIOOOOOO => refl_equal ([||w8_WW OIOOOOOO l||])
 | OIOOOOOI => refl_equal ([||w8_WW OIOOOOOI l||])
 | OIOOOOIO => refl_equal ([||w8_WW OIOOOOIO l||])
 | OIOOOOII => refl_equal ([||w8_WW OIOOOOII l||])
 | OIOOOIOO => refl_equal ([||w8_WW OIOOOIOO l||])
 | OIOOOIOI => refl_equal ([||w8_WW OIOOOIOI l||])
 | OIOOOIIO => refl_equal ([||w8_WW OIOOOIIO l||])
 | OIOOOIII => refl_equal ([||w8_WW OIOOOIII l||])
 | OIOOIOOO => refl_equal ([||w8_WW OIOOIOOO l||])
 | OIOOIOOI => refl_equal ([||w8_WW OIOOIOOI l||])
 | OIOOIOIO => refl_equal ([||w8_WW OIOOIOIO l||])
 | OIOOIOII => refl_equal ([||w8_WW OIOOIOII l||])
 | OIOOIIOO => refl_equal ([||w8_WW OIOOIIOO l||])
 | OIOOIIOI => refl_equal ([||w8_WW OIOOIIOI l||])
 | OIOOIIIO => refl_equal ([||w8_WW OIOOIIIO l||])
 | OIOOIIII => refl_equal ([||w8_WW OIOOIIII l||])
 | OIOIOOOO => refl_equal ([||w8_WW OIOIOOOO l||])
 | OIOIOOOI => refl_equal ([||w8_WW OIOIOOOI l||])
 | OIOIOOIO => refl_equal ([||w8_WW OIOIOOIO l||])
 | OIOIOOII => refl_equal ([||w8_WW OIOIOOII l||])
 | OIOIOIOO => refl_equal ([||w8_WW OIOIOIOO l||])
 | OIOIOIOI => refl_equal ([||w8_WW OIOIOIOI l||])
 | OIOIOIIO => refl_equal ([||w8_WW OIOIOIIO l||])
 | OIOIOIII => refl_equal ([||w8_WW OIOIOIII l||])
 | OIOIIOOO => refl_equal ([||w8_WW OIOIIOOO l||])
 | OIOIIOOI => refl_equal ([||w8_WW OIOIIOOI l||])
 | OIOIIOIO => refl_equal ([||w8_WW OIOIIOIO l||])
 | OIOIIOII => refl_equal ([||w8_WW OIOIIOII l||])
 | OIOIIIOO => refl_equal ([||w8_WW OIOIIIOO l||])
 | OIOIIIOI => refl_equal ([||w8_WW OIOIIIOI l||])
 | OIOIIIIO => refl_equal ([||w8_WW OIOIIIIO l||])
 | OIOIIIII => refl_equal ([||w8_WW OIOIIIII l||])
 | OIIOOOOO => refl_equal ([||w8_WW OIIOOOOO l||])
 | OIIOOOOI => refl_equal ([||w8_WW OIIOOOOI l||])
 | OIIOOOIO => refl_equal ([||w8_WW OIIOOOIO l||])
 | OIIOOOII => refl_equal ([||w8_WW OIIOOOII l||])
 | OIIOOIOO => refl_equal ([||w8_WW OIIOOIOO l||])
 | OIIOOIOI => refl_equal ([||w8_WW OIIOOIOI l||])
 | OIIOOIIO => refl_equal ([||w8_WW OIIOOIIO l||])
 | OIIOOIII => refl_equal ([||w8_WW OIIOOIII l||])
 | OIIOIOOO => refl_equal ([||w8_WW OIIOIOOO l||])
 | OIIOIOOI => refl_equal ([||w8_WW OIIOIOOI l||])
 | OIIOIOIO => refl_equal ([||w8_WW OIIOIOIO l||])
 | OIIOIOII => refl_equal ([||w8_WW OIIOIOII l||])
 | OIIOIIOO => refl_equal ([||w8_WW OIIOIIOO l||])
 | OIIOIIOI => refl_equal ([||w8_WW OIIOIIOI l||])
 | OIIOIIIO => refl_equal ([||w8_WW OIIOIIIO l||])
 | OIIOIIII => refl_equal ([||w8_WW OIIOIIII l||])
 | OIIIOOOO => refl_equal ([||w8_WW OIIIOOOO l||])
 | OIIIOOOI => refl_equal ([||w8_WW OIIIOOOI l||])
 | OIIIOOIO => refl_equal ([||w8_WW OIIIOOIO l||])
 | OIIIOOII => refl_equal ([||w8_WW OIIIOOII l||])
 | OIIIOIOO => refl_equal ([||w8_WW OIIIOIOO l||])
 | OIIIOIOI => refl_equal ([||w8_WW OIIIOIOI l||])
 | OIIIOIIO => refl_equal ([||w8_WW OIIIOIIO l||])
 | OIIIOIII => refl_equal ([||w8_WW OIIIOIII l||])
 | OIIIIOOO => refl_equal ([||w8_WW OIIIIOOO l||])
 | OIIIIOOI => refl_equal ([||w8_WW OIIIIOOI l||])
 | OIIIIOIO => refl_equal ([||w8_WW OIIIIOIO l||])
 | OIIIIOII => refl_equal ([||w8_WW OIIIIOII l||])
 | OIIIIIOO => refl_equal ([||w8_WW OIIIIIOO l||])
 | OIIIIIOI => refl_equal ([||w8_WW OIIIIIOI l||])
 | OIIIIIIO => refl_equal ([||w8_WW OIIIIIIO l||])
 | OIIIIIII => refl_equal ([||w8_WW OIIIIIII l||])
 | IOOOOOOO => refl_equal ([||w8_WW IOOOOOOO l||])
 | IOOOOOOI => refl_equal ([||w8_WW IOOOOOOI l||])
 | IOOOOOIO => refl_equal ([||w8_WW IOOOOOIO l||])
 | IOOOOOII => refl_equal ([||w8_WW IOOOOOII l||])
 | IOOOOIOO => refl_equal ([||w8_WW IOOOOIOO l||])
 | IOOOOIOI => refl_equal ([||w8_WW IOOOOIOI l||])
 | IOOOOIIO => refl_equal ([||w8_WW IOOOOIIO l||])
 | IOOOOIII => refl_equal ([||w8_WW IOOOOIII l||])
 | IOOOIOOO => refl_equal ([||w8_WW IOOOIOOO l||])
 | IOOOIOOI => refl_equal ([||w8_WW IOOOIOOI l||])
 | IOOOIOIO => refl_equal ([||w8_WW IOOOIOIO l||])
 | IOOOIOII => refl_equal ([||w8_WW IOOOIOII l||])
 | IOOOIIOO => refl_equal ([||w8_WW IOOOIIOO l||])
 | IOOOIIOI => refl_equal ([||w8_WW IOOOIIOI l||])
 | IOOOIIIO => refl_equal ([||w8_WW IOOOIIIO l||])
 | IOOOIIII => refl_equal ([||w8_WW IOOOIIII l||])
 | IOOIOOOO => refl_equal ([||w8_WW IOOIOOOO l||])
 | IOOIOOOI => refl_equal ([||w8_WW IOOIOOOI l||])
 | IOOIOOIO => refl_equal ([||w8_WW IOOIOOIO l||])
 | IOOIOOII => refl_equal ([||w8_WW IOOIOOII l||])
 | IOOIOIOO => refl_equal ([||w8_WW IOOIOIOO l||])
 | IOOIOIOI => refl_equal ([||w8_WW IOOIOIOI l||])
 | IOOIOIIO => refl_equal ([||w8_WW IOOIOIIO l||])
 | IOOIOIII => refl_equal ([||w8_WW IOOIOIII l||])
 | IOOIIOOO => refl_equal ([||w8_WW IOOIIOOO l||])
 | IOOIIOOI => refl_equal ([||w8_WW IOOIIOOI l||])
 | IOOIIOIO => refl_equal ([||w8_WW IOOIIOIO l||])
 | IOOIIOII => refl_equal ([||w8_WW IOOIIOII l||])
 | IOOIIIOO => refl_equal ([||w8_WW IOOIIIOO l||])
 | IOOIIIOI => refl_equal ([||w8_WW IOOIIIOI l||])
 | IOOIIIIO => refl_equal ([||w8_WW IOOIIIIO l||])
 | IOOIIIII => refl_equal ([||w8_WW IOOIIIII l||])
 | IOIOOOOO => refl_equal ([||w8_WW IOIOOOOO l||])
 | IOIOOOOI => refl_equal ([||w8_WW IOIOOOOI l||])
 | IOIOOOIO => refl_equal ([||w8_WW IOIOOOIO l||])
 | IOIOOOII => refl_equal ([||w8_WW IOIOOOII l||])
 | IOIOOIOO => refl_equal ([||w8_WW IOIOOIOO l||])
 | IOIOOIOI => refl_equal ([||w8_WW IOIOOIOI l||])
 | IOIOOIIO => refl_equal ([||w8_WW IOIOOIIO l||])
 | IOIOOIII => refl_equal ([||w8_WW IOIOOIII l||])
 | IOIOIOOO => refl_equal ([||w8_WW IOIOIOOO l||])
 | IOIOIOOI => refl_equal ([||w8_WW IOIOIOOI l||])
 | IOIOIOIO => refl_equal ([||w8_WW IOIOIOIO l||])
 | IOIOIOII => refl_equal ([||w8_WW IOIOIOII l||])
 | IOIOIIOO => refl_equal ([||w8_WW IOIOIIOO l||])
 | IOIOIIOI => refl_equal ([||w8_WW IOIOIIOI l||])
 | IOIOIIIO => refl_equal ([||w8_WW IOIOIIIO l||])
 | IOIOIIII => refl_equal ([||w8_WW IOIOIIII l||])
 | IOIIOOOO => refl_equal ([||w8_WW IOIIOOOO l||])
 | IOIIOOOI => refl_equal ([||w8_WW IOIIOOOI l||])
 | IOIIOOIO => refl_equal ([||w8_WW IOIIOOIO l||])
 | IOIIOOII => refl_equal ([||w8_WW IOIIOOII l||])
 | IOIIOIOO => refl_equal ([||w8_WW IOIIOIOO l||])
 | IOIIOIOI => refl_equal ([||w8_WW IOIIOIOI l||])
 | IOIIOIIO => refl_equal ([||w8_WW IOIIOIIO l||])
 | IOIIOIII => refl_equal ([||w8_WW IOIIOIII l||])
 | IOIIIOOO => refl_equal ([||w8_WW IOIIIOOO l||])
 | IOIIIOOI => refl_equal ([||w8_WW IOIIIOOI l||])
 | IOIIIOIO => refl_equal ([||w8_WW IOIIIOIO l||])
 | IOIIIOII => refl_equal ([||w8_WW IOIIIOII l||])
 | IOIIIIOO => refl_equal ([||w8_WW IOIIIIOO l||])
 | IOIIIIOI => refl_equal ([||w8_WW IOIIIIOI l||])
 | IOIIIIIO => refl_equal ([||w8_WW IOIIIIIO l||])
 | IOIIIIII => refl_equal ([||w8_WW IOIIIIII l||])
 | IIOOOOOO => refl_equal ([||w8_WW IIOOOOOO l||])
 | IIOOOOOI => refl_equal ([||w8_WW IIOOOOOI l||])
 | IIOOOOIO => refl_equal ([||w8_WW IIOOOOIO l||])
 | IIOOOOII => refl_equal ([||w8_WW IIOOOOII l||])
 | IIOOOIOO => refl_equal ([||w8_WW IIOOOIOO l||])
 | IIOOOIOI => refl_equal ([||w8_WW IIOOOIOI l||])
 | IIOOOIIO => refl_equal ([||w8_WW IIOOOIIO l||])
 | IIOOOIII => refl_equal ([||w8_WW IIOOOIII l||])
 | IIOOIOOO => refl_equal ([||w8_WW IIOOIOOO l||])
 | IIOOIOOI => refl_equal ([||w8_WW IIOOIOOI l||])
 | IIOOIOIO => refl_equal ([||w8_WW IIOOIOIO l||])
 | IIOOIOII => refl_equal ([||w8_WW IIOOIOII l||])
 | IIOOIIOO => refl_equal ([||w8_WW IIOOIIOO l||])
 | IIOOIIOI => refl_equal ([||w8_WW IIOOIIOI l||])
 | IIOOIIIO => refl_equal ([||w8_WW IIOOIIIO l||])
 | IIOOIIII => refl_equal ([||w8_WW IIOOIIII l||])
 | IIOIOOOO => refl_equal ([||w8_WW IIOIOOOO l||])
 | IIOIOOOI => refl_equal ([||w8_WW IIOIOOOI l||])
 | IIOIOOIO => refl_equal ([||w8_WW IIOIOOIO l||])
 | IIOIOOII => refl_equal ([||w8_WW IIOIOOII l||])
 | IIOIOIOO => refl_equal ([||w8_WW IIOIOIOO l||])
 | IIOIOIOI => refl_equal ([||w8_WW IIOIOIOI l||])
 | IIOIOIIO => refl_equal ([||w8_WW IIOIOIIO l||])
 | IIOIOIII => refl_equal ([||w8_WW IIOIOIII l||])
 | IIOIIOOO => refl_equal ([||w8_WW IIOIIOOO l||])
 | IIOIIOOI => refl_equal ([||w8_WW IIOIIOOI l||])
 | IIOIIOIO => refl_equal ([||w8_WW IIOIIOIO l||])
 | IIOIIOII => refl_equal ([||w8_WW IIOIIOII l||])
 | IIOIIIOO => refl_equal ([||w8_WW IIOIIIOO l||])
 | IIOIIIOI => refl_equal ([||w8_WW IIOIIIOI l||])
 | IIOIIIIO => refl_equal ([||w8_WW IIOIIIIO l||])
 | IIOIIIII => refl_equal ([||w8_WW IIOIIIII l||])
 | IIIOOOOO => refl_equal ([||w8_WW IIIOOOOO l||])
 | IIIOOOOI => refl_equal ([||w8_WW IIIOOOOI l||])
 | IIIOOOIO => refl_equal ([||w8_WW IIIOOOIO l||])
 | IIIOOOII => refl_equal ([||w8_WW IIIOOOII l||])
 | IIIOOIOO => refl_equal ([||w8_WW IIIOOIOO l||])
 | IIIOOIOI => refl_equal ([||w8_WW IIIOOIOI l||])
 | IIIOOIIO => refl_equal ([||w8_WW IIIOOIIO l||])
 | IIIOOIII => refl_equal ([||w8_WW IIIOOIII l||])
 | IIIOIOOO => refl_equal ([||w8_WW IIIOIOOO l||])
 | IIIOIOOI => refl_equal ([||w8_WW IIIOIOOI l||])
 | IIIOIOIO => refl_equal ([||w8_WW IIIOIOIO l||])
 | IIIOIOII => refl_equal ([||w8_WW IIIOIOII l||])
 | IIIOIIOO => refl_equal ([||w8_WW IIIOIIOO l||])
 | IIIOIIOI => refl_equal ([||w8_WW IIIOIIOI l||])
 | IIIOIIIO => refl_equal ([||w8_WW IIIOIIIO l||])
 | IIIOIIII => refl_equal ([||w8_WW IIIOIIII l||])
 | IIIIOOOO => refl_equal ([||w8_WW IIIIOOOO l||])
 | IIIIOOOI => refl_equal ([||w8_WW IIIIOOOI l||])
 | IIIIOOIO => refl_equal ([||w8_WW IIIIOOIO l||])
 | IIIIOOII => refl_equal ([||w8_WW IIIIOOII l||])
 | IIIIOIOO => refl_equal ([||w8_WW IIIIOIOO l||])
 | IIIIOIOI => refl_equal ([||w8_WW IIIIOIOI l||])
 | IIIIOIIO => refl_equal ([||w8_WW IIIIOIIO l||])
 | IIIIOIII => refl_equal ([||w8_WW IIIIOIII l||])
 | IIIIIOOO => refl_equal ([||w8_WW IIIIIOOO l||])
 | IIIIIOOI => refl_equal ([||w8_WW IIIIIOOI l||])
 | IIIIIOIO => refl_equal ([||w8_WW IIIIIOIO l||])
 | IIIIIOII => refl_equal ([||w8_WW IIIIIOII l||])
 | IIIIIIOO => refl_equal ([||w8_WW IIIIIIOO l||])
 | IIIIIIOI => refl_equal ([||w8_WW IIIIIIOI l||])
 | IIIIIIIO => refl_equal ([||w8_WW IIIIIIIO l||])
 | IIIIIIII => refl_equal ([||w8_WW IIIIIIII l||])
 end.

Lemma w8_CW_spec : forall sign c l, interp_carry sign (w8_B*w8_B) (zn2z_to_Z w8_B w8_to_Z) (w8_CW c l) = (interp_carry sign w8_B w8_to_Z c)*w8_B + [|l|].
Proof.
intros sign c l;case c;intro h;simpl;fold (w8_WW h l); rewrite w8_WW_spec;unfold w8_B; ring.
Qed.

