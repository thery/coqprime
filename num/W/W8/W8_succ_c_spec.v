Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Open Local Scope w8_scope.
Require Import W8_add.


Lemma w8_succ_c_spec : forall x, [+|w8_succ_c x|] = [|x|] + 1.
Proof
fun x =>
 match x as x return [+|w8_succ_c x|] = [|x|] + 1 with
 | OOOOOOOO => refl_equal (0+1)
 | OOOOOOOI => refl_equal (1+1)
 | OOOOOOIO => refl_equal (2+1)
 | OOOOOOII => refl_equal (3+1)
 | OOOOOIOO => refl_equal (4+1)
 | OOOOOIOI => refl_equal (5+1)
 | OOOOOIIO => refl_equal (6+1)
 | OOOOOIII => refl_equal (7+1)
 | OOOOIOOO => refl_equal (8+1)
 | OOOOIOOI => refl_equal (9+1)
 | OOOOIOIO => refl_equal (10+1)
 | OOOOIOII => refl_equal (11+1)
 | OOOOIIOO => refl_equal (12+1)
 | OOOOIIOI => refl_equal (13+1)
 | OOOOIIIO => refl_equal (14+1)
 | OOOOIIII => refl_equal (15+1)
 | OOOIOOOO => refl_equal (16+1)
 | OOOIOOOI => refl_equal (17+1)
 | OOOIOOIO => refl_equal (18+1)
 | OOOIOOII => refl_equal (19+1)
 | OOOIOIOO => refl_equal (20+1)
 | OOOIOIOI => refl_equal (21+1)
 | OOOIOIIO => refl_equal (22+1)
 | OOOIOIII => refl_equal (23+1)
 | OOOIIOOO => refl_equal (24+1)
 | OOOIIOOI => refl_equal (25+1)
 | OOOIIOIO => refl_equal (26+1)
 | OOOIIOII => refl_equal (27+1)
 | OOOIIIOO => refl_equal (28+1)
 | OOOIIIOI => refl_equal (29+1)
 | OOOIIIIO => refl_equal (30+1)
 | OOOIIIII => refl_equal (31+1)
 | OOIOOOOO => refl_equal (32+1)
 | OOIOOOOI => refl_equal (33+1)
 | OOIOOOIO => refl_equal (34+1)
 | OOIOOOII => refl_equal (35+1)
 | OOIOOIOO => refl_equal (36+1)
 | OOIOOIOI => refl_equal (37+1)
 | OOIOOIIO => refl_equal (38+1)
 | OOIOOIII => refl_equal (39+1)
 | OOIOIOOO => refl_equal (40+1)
 | OOIOIOOI => refl_equal (41+1)
 | OOIOIOIO => refl_equal (42+1)
 | OOIOIOII => refl_equal (43+1)
 | OOIOIIOO => refl_equal (44+1)
 | OOIOIIOI => refl_equal (45+1)
 | OOIOIIIO => refl_equal (46+1)
 | OOIOIIII => refl_equal (47+1)
 | OOIIOOOO => refl_equal (48+1)
 | OOIIOOOI => refl_equal (49+1)
 | OOIIOOIO => refl_equal (50+1)
 | OOIIOOII => refl_equal (51+1)
 | OOIIOIOO => refl_equal (52+1)
 | OOIIOIOI => refl_equal (53+1)
 | OOIIOIIO => refl_equal (54+1)
 | OOIIOIII => refl_equal (55+1)
 | OOIIIOOO => refl_equal (56+1)
 | OOIIIOOI => refl_equal (57+1)
 | OOIIIOIO => refl_equal (58+1)
 | OOIIIOII => refl_equal (59+1)
 | OOIIIIOO => refl_equal (60+1)
 | OOIIIIOI => refl_equal (61+1)
 | OOIIIIIO => refl_equal (62+1)
 | OOIIIIII => refl_equal (63+1)
 | OIOOOOOO => refl_equal (64+1)
 | OIOOOOOI => refl_equal (65+1)
 | OIOOOOIO => refl_equal (66+1)
 | OIOOOOII => refl_equal (67+1)
 | OIOOOIOO => refl_equal (68+1)
 | OIOOOIOI => refl_equal (69+1)
 | OIOOOIIO => refl_equal (70+1)
 | OIOOOIII => refl_equal (71+1)
 | OIOOIOOO => refl_equal (72+1)
 | OIOOIOOI => refl_equal (73+1)
 | OIOOIOIO => refl_equal (74+1)
 | OIOOIOII => refl_equal (75+1)
 | OIOOIIOO => refl_equal (76+1)
 | OIOOIIOI => refl_equal (77+1)
 | OIOOIIIO => refl_equal (78+1)
 | OIOOIIII => refl_equal (79+1)
 | OIOIOOOO => refl_equal (80+1)
 | OIOIOOOI => refl_equal (81+1)
 | OIOIOOIO => refl_equal (82+1)
 | OIOIOOII => refl_equal (83+1)
 | OIOIOIOO => refl_equal (84+1)
 | OIOIOIOI => refl_equal (85+1)
 | OIOIOIIO => refl_equal (86+1)
 | OIOIOIII => refl_equal (87+1)
 | OIOIIOOO => refl_equal (88+1)
 | OIOIIOOI => refl_equal (89+1)
 | OIOIIOIO => refl_equal (90+1)
 | OIOIIOII => refl_equal (91+1)
 | OIOIIIOO => refl_equal (92+1)
 | OIOIIIOI => refl_equal (93+1)
 | OIOIIIIO => refl_equal (94+1)
 | OIOIIIII => refl_equal (95+1)
 | OIIOOOOO => refl_equal (96+1)
 | OIIOOOOI => refl_equal (97+1)
 | OIIOOOIO => refl_equal (98+1)
 | OIIOOOII => refl_equal (99+1)
 | OIIOOIOO => refl_equal (100+1)
 | OIIOOIOI => refl_equal (101+1)
 | OIIOOIIO => refl_equal (102+1)
 | OIIOOIII => refl_equal (103+1)
 | OIIOIOOO => refl_equal (104+1)
 | OIIOIOOI => refl_equal (105+1)
 | OIIOIOIO => refl_equal (106+1)
 | OIIOIOII => refl_equal (107+1)
 | OIIOIIOO => refl_equal (108+1)
 | OIIOIIOI => refl_equal (109+1)
 | OIIOIIIO => refl_equal (110+1)
 | OIIOIIII => refl_equal (111+1)
 | OIIIOOOO => refl_equal (112+1)
 | OIIIOOOI => refl_equal (113+1)
 | OIIIOOIO => refl_equal (114+1)
 | OIIIOOII => refl_equal (115+1)
 | OIIIOIOO => refl_equal (116+1)
 | OIIIOIOI => refl_equal (117+1)
 | OIIIOIIO => refl_equal (118+1)
 | OIIIOIII => refl_equal (119+1)
 | OIIIIOOO => refl_equal (120+1)
 | OIIIIOOI => refl_equal (121+1)
 | OIIIIOIO => refl_equal (122+1)
 | OIIIIOII => refl_equal (123+1)
 | OIIIIIOO => refl_equal (124+1)
 | OIIIIIOI => refl_equal (125+1)
 | OIIIIIIO => refl_equal (126+1)
 | OIIIIIII => refl_equal (127+1)
 | IOOOOOOO => refl_equal (128+1)
 | IOOOOOOI => refl_equal (129+1)
 | IOOOOOIO => refl_equal (130+1)
 | IOOOOOII => refl_equal (131+1)
 | IOOOOIOO => refl_equal (132+1)
 | IOOOOIOI => refl_equal (133+1)
 | IOOOOIIO => refl_equal (134+1)
 | IOOOOIII => refl_equal (135+1)
 | IOOOIOOO => refl_equal (136+1)
 | IOOOIOOI => refl_equal (137+1)
 | IOOOIOIO => refl_equal (138+1)
 | IOOOIOII => refl_equal (139+1)
 | IOOOIIOO => refl_equal (140+1)
 | IOOOIIOI => refl_equal (141+1)
 | IOOOIIIO => refl_equal (142+1)
 | IOOOIIII => refl_equal (143+1)
 | IOOIOOOO => refl_equal (144+1)
 | IOOIOOOI => refl_equal (145+1)
 | IOOIOOIO => refl_equal (146+1)
 | IOOIOOII => refl_equal (147+1)
 | IOOIOIOO => refl_equal (148+1)
 | IOOIOIOI => refl_equal (149+1)
 | IOOIOIIO => refl_equal (150+1)
 | IOOIOIII => refl_equal (151+1)
 | IOOIIOOO => refl_equal (152+1)
 | IOOIIOOI => refl_equal (153+1)
 | IOOIIOIO => refl_equal (154+1)
 | IOOIIOII => refl_equal (155+1)
 | IOOIIIOO => refl_equal (156+1)
 | IOOIIIOI => refl_equal (157+1)
 | IOOIIIIO => refl_equal (158+1)
 | IOOIIIII => refl_equal (159+1)
 | IOIOOOOO => refl_equal (160+1)
 | IOIOOOOI => refl_equal (161+1)
 | IOIOOOIO => refl_equal (162+1)
 | IOIOOOII => refl_equal (163+1)
 | IOIOOIOO => refl_equal (164+1)
 | IOIOOIOI => refl_equal (165+1)
 | IOIOOIIO => refl_equal (166+1)
 | IOIOOIII => refl_equal (167+1)
 | IOIOIOOO => refl_equal (168+1)
 | IOIOIOOI => refl_equal (169+1)
 | IOIOIOIO => refl_equal (170+1)
 | IOIOIOII => refl_equal (171+1)
 | IOIOIIOO => refl_equal (172+1)
 | IOIOIIOI => refl_equal (173+1)
 | IOIOIIIO => refl_equal (174+1)
 | IOIOIIII => refl_equal (175+1)
 | IOIIOOOO => refl_equal (176+1)
 | IOIIOOOI => refl_equal (177+1)
 | IOIIOOIO => refl_equal (178+1)
 | IOIIOOII => refl_equal (179+1)
 | IOIIOIOO => refl_equal (180+1)
 | IOIIOIOI => refl_equal (181+1)
 | IOIIOIIO => refl_equal (182+1)
 | IOIIOIII => refl_equal (183+1)
 | IOIIIOOO => refl_equal (184+1)
 | IOIIIOOI => refl_equal (185+1)
 | IOIIIOIO => refl_equal (186+1)
 | IOIIIOII => refl_equal (187+1)
 | IOIIIIOO => refl_equal (188+1)
 | IOIIIIOI => refl_equal (189+1)
 | IOIIIIIO => refl_equal (190+1)
 | IOIIIIII => refl_equal (191+1)
 | IIOOOOOO => refl_equal (192+1)
 | IIOOOOOI => refl_equal (193+1)
 | IIOOOOIO => refl_equal (194+1)
 | IIOOOOII => refl_equal (195+1)
 | IIOOOIOO => refl_equal (196+1)
 | IIOOOIOI => refl_equal (197+1)
 | IIOOOIIO => refl_equal (198+1)
 | IIOOOIII => refl_equal (199+1)
 | IIOOIOOO => refl_equal (200+1)
 | IIOOIOOI => refl_equal (201+1)
 | IIOOIOIO => refl_equal (202+1)
 | IIOOIOII => refl_equal (203+1)
 | IIOOIIOO => refl_equal (204+1)
 | IIOOIIOI => refl_equal (205+1)
 | IIOOIIIO => refl_equal (206+1)
 | IIOOIIII => refl_equal (207+1)
 | IIOIOOOO => refl_equal (208+1)
 | IIOIOOOI => refl_equal (209+1)
 | IIOIOOIO => refl_equal (210+1)
 | IIOIOOII => refl_equal (211+1)
 | IIOIOIOO => refl_equal (212+1)
 | IIOIOIOI => refl_equal (213+1)
 | IIOIOIIO => refl_equal (214+1)
 | IIOIOIII => refl_equal (215+1)
 | IIOIIOOO => refl_equal (216+1)
 | IIOIIOOI => refl_equal (217+1)
 | IIOIIOIO => refl_equal (218+1)
 | IIOIIOII => refl_equal (219+1)
 | IIOIIIOO => refl_equal (220+1)
 | IIOIIIOI => refl_equal (221+1)
 | IIOIIIIO => refl_equal (222+1)
 | IIOIIIII => refl_equal (223+1)
 | IIIOOOOO => refl_equal (224+1)
 | IIIOOOOI => refl_equal (225+1)
 | IIIOOOIO => refl_equal (226+1)
 | IIIOOOII => refl_equal (227+1)
 | IIIOOIOO => refl_equal (228+1)
 | IIIOOIOI => refl_equal (229+1)
 | IIIOOIIO => refl_equal (230+1)
 | IIIOOIII => refl_equal (231+1)
 | IIIOIOOO => refl_equal (232+1)
 | IIIOIOOI => refl_equal (233+1)
 | IIIOIOIO => refl_equal (234+1)
 | IIIOIOII => refl_equal (235+1)
 | IIIOIIOO => refl_equal (236+1)
 | IIIOIIOI => refl_equal (237+1)
 | IIIOIIIO => refl_equal (238+1)
 | IIIOIIII => refl_equal (239+1)
 | IIIIOOOO => refl_equal (240+1)
 | IIIIOOOI => refl_equal (241+1)
 | IIIIOOIO => refl_equal (242+1)
 | IIIIOOII => refl_equal (243+1)
 | IIIIOIOO => refl_equal (244+1)
 | IIIIOIOI => refl_equal (245+1)
 | IIIIOIIO => refl_equal (246+1)
 | IIIIOIII => refl_equal (247+1)
 | IIIIIOOO => refl_equal (248+1)
 | IIIIIOOI => refl_equal (249+1)
 | IIIIIOIO => refl_equal (250+1)
 | IIIIIOII => refl_equal (251+1)
 | IIIIIIOO => refl_equal (252+1)
 | IIIIIIOI => refl_equal (253+1)
 | IIIIIIIO => refl_equal (254+1)
 | IIIIIIII => refl_equal (255+1)
 end.

Lemma w8_carry_succ_c_spec : forall c, [+|c|] <= w8_B + (w8_B - 2) -> [+|w8_carry_succ_c c|] = [+|c|] + 1.
Proof
fun c =>
 match c as c return [+|c|] <= w8_B + (w8_B - 2) -> [+|w8_carry_succ_c c|] = [+|c|] + 1 with
 | C0 x => fun (H:[+|C0 x|] <= w8_B + (w8_B - 2))=> w8_succ_c_spec x
 | C1 x =>
    match x as x return [+|(C1 x)|] <= w8_B + (w8_B - 2) -> [+|w8_carry_succ_c (C1 x)|] = [+|(C1 x)|] + 1 with
    | OOOOOOOO => fun (H:[+|C1 OOOOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 257
    | OOOOOOOI => fun (H:[+|C1 OOOOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 258
    | OOOOOOIO => fun (H:[+|C1 OOOOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 259
    | OOOOOOII => fun (H:[+|C1 OOOOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 260
    | OOOOOIOO => fun (H:[+|C1 OOOOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 261
    | OOOOOIOI => fun (H:[+|C1 OOOOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 262
    | OOOOOIIO => fun (H:[+|C1 OOOOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 263
    | OOOOOIII => fun (H:[+|C1 OOOOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 264
    | OOOOIOOO => fun (H:[+|C1 OOOOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 265
    | OOOOIOOI => fun (H:[+|C1 OOOOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 266
    | OOOOIOIO => fun (H:[+|C1 OOOOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 267
    | OOOOIOII => fun (H:[+|C1 OOOOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 268
    | OOOOIIOO => fun (H:[+|C1 OOOOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 269
    | OOOOIIOI => fun (H:[+|C1 OOOOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 270
    | OOOOIIIO => fun (H:[+|C1 OOOOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 271
    | OOOOIIII => fun (H:[+|C1 OOOOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 272
    | OOOIOOOO => fun (H:[+|C1 OOOIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 273
    | OOOIOOOI => fun (H:[+|C1 OOOIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 274
    | OOOIOOIO => fun (H:[+|C1 OOOIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 275
    | OOOIOOII => fun (H:[+|C1 OOOIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 276
    | OOOIOIOO => fun (H:[+|C1 OOOIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 277
    | OOOIOIOI => fun (H:[+|C1 OOOIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 278
    | OOOIOIIO => fun (H:[+|C1 OOOIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 279
    | OOOIOIII => fun (H:[+|C1 OOOIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 280
    | OOOIIOOO => fun (H:[+|C1 OOOIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 281
    | OOOIIOOI => fun (H:[+|C1 OOOIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 282
    | OOOIIOIO => fun (H:[+|C1 OOOIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 283
    | OOOIIOII => fun (H:[+|C1 OOOIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 284
    | OOOIIIOO => fun (H:[+|C1 OOOIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 285
    | OOOIIIOI => fun (H:[+|C1 OOOIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 286
    | OOOIIIIO => fun (H:[+|C1 OOOIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 287
    | OOOIIIII => fun (H:[+|C1 OOOIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 288
    | OOIOOOOO => fun (H:[+|C1 OOIOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 289
    | OOIOOOOI => fun (H:[+|C1 OOIOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 290
    | OOIOOOIO => fun (H:[+|C1 OOIOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 291
    | OOIOOOII => fun (H:[+|C1 OOIOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 292
    | OOIOOIOO => fun (H:[+|C1 OOIOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 293
    | OOIOOIOI => fun (H:[+|C1 OOIOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 294
    | OOIOOIIO => fun (H:[+|C1 OOIOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 295
    | OOIOOIII => fun (H:[+|C1 OOIOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 296
    | OOIOIOOO => fun (H:[+|C1 OOIOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 297
    | OOIOIOOI => fun (H:[+|C1 OOIOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 298
    | OOIOIOIO => fun (H:[+|C1 OOIOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 299
    | OOIOIOII => fun (H:[+|C1 OOIOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 300
    | OOIOIIOO => fun (H:[+|C1 OOIOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 301
    | OOIOIIOI => fun (H:[+|C1 OOIOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 302
    | OOIOIIIO => fun (H:[+|C1 OOIOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 303
    | OOIOIIII => fun (H:[+|C1 OOIOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 304
    | OOIIOOOO => fun (H:[+|C1 OOIIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 305
    | OOIIOOOI => fun (H:[+|C1 OOIIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 306
    | OOIIOOIO => fun (H:[+|C1 OOIIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 307
    | OOIIOOII => fun (H:[+|C1 OOIIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 308
    | OOIIOIOO => fun (H:[+|C1 OOIIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 309
    | OOIIOIOI => fun (H:[+|C1 OOIIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 310
    | OOIIOIIO => fun (H:[+|C1 OOIIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 311
    | OOIIOIII => fun (H:[+|C1 OOIIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 312
    | OOIIIOOO => fun (H:[+|C1 OOIIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 313
    | OOIIIOOI => fun (H:[+|C1 OOIIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 314
    | OOIIIOIO => fun (H:[+|C1 OOIIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 315
    | OOIIIOII => fun (H:[+|C1 OOIIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 316
    | OOIIIIOO => fun (H:[+|C1 OOIIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 317
    | OOIIIIOI => fun (H:[+|C1 OOIIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 318
    | OOIIIIIO => fun (H:[+|C1 OOIIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 319
    | OOIIIIII => fun (H:[+|C1 OOIIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 320
    | OIOOOOOO => fun (H:[+|C1 OIOOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 321
    | OIOOOOOI => fun (H:[+|C1 OIOOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 322
    | OIOOOOIO => fun (H:[+|C1 OIOOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 323
    | OIOOOOII => fun (H:[+|C1 OIOOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 324
    | OIOOOIOO => fun (H:[+|C1 OIOOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 325
    | OIOOOIOI => fun (H:[+|C1 OIOOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 326
    | OIOOOIIO => fun (H:[+|C1 OIOOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 327
    | OIOOOIII => fun (H:[+|C1 OIOOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 328
    | OIOOIOOO => fun (H:[+|C1 OIOOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 329
    | OIOOIOOI => fun (H:[+|C1 OIOOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 330
    | OIOOIOIO => fun (H:[+|C1 OIOOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 331
    | OIOOIOII => fun (H:[+|C1 OIOOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 332
    | OIOOIIOO => fun (H:[+|C1 OIOOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 333
    | OIOOIIOI => fun (H:[+|C1 OIOOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 334
    | OIOOIIIO => fun (H:[+|C1 OIOOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 335
    | OIOOIIII => fun (H:[+|C1 OIOOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 336
    | OIOIOOOO => fun (H:[+|C1 OIOIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 337
    | OIOIOOOI => fun (H:[+|C1 OIOIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 338
    | OIOIOOIO => fun (H:[+|C1 OIOIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 339
    | OIOIOOII => fun (H:[+|C1 OIOIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 340
    | OIOIOIOO => fun (H:[+|C1 OIOIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 341
    | OIOIOIOI => fun (H:[+|C1 OIOIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 342
    | OIOIOIIO => fun (H:[+|C1 OIOIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 343
    | OIOIOIII => fun (H:[+|C1 OIOIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 344
    | OIOIIOOO => fun (H:[+|C1 OIOIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 345
    | OIOIIOOI => fun (H:[+|C1 OIOIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 346
    | OIOIIOIO => fun (H:[+|C1 OIOIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 347
    | OIOIIOII => fun (H:[+|C1 OIOIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 348
    | OIOIIIOO => fun (H:[+|C1 OIOIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 349
    | OIOIIIOI => fun (H:[+|C1 OIOIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 350
    | OIOIIIIO => fun (H:[+|C1 OIOIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 351
    | OIOIIIII => fun (H:[+|C1 OIOIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 352
    | OIIOOOOO => fun (H:[+|C1 OIIOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 353
    | OIIOOOOI => fun (H:[+|C1 OIIOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 354
    | OIIOOOIO => fun (H:[+|C1 OIIOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 355
    | OIIOOOII => fun (H:[+|C1 OIIOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 356
    | OIIOOIOO => fun (H:[+|C1 OIIOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 357
    | OIIOOIOI => fun (H:[+|C1 OIIOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 358
    | OIIOOIIO => fun (H:[+|C1 OIIOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 359
    | OIIOOIII => fun (H:[+|C1 OIIOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 360
    | OIIOIOOO => fun (H:[+|C1 OIIOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 361
    | OIIOIOOI => fun (H:[+|C1 OIIOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 362
    | OIIOIOIO => fun (H:[+|C1 OIIOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 363
    | OIIOIOII => fun (H:[+|C1 OIIOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 364
    | OIIOIIOO => fun (H:[+|C1 OIIOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 365
    | OIIOIIOI => fun (H:[+|C1 OIIOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 366
    | OIIOIIIO => fun (H:[+|C1 OIIOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 367
    | OIIOIIII => fun (H:[+|C1 OIIOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 368
    | OIIIOOOO => fun (H:[+|C1 OIIIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 369
    | OIIIOOOI => fun (H:[+|C1 OIIIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 370
    | OIIIOOIO => fun (H:[+|C1 OIIIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 371
    | OIIIOOII => fun (H:[+|C1 OIIIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 372
    | OIIIOIOO => fun (H:[+|C1 OIIIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 373
    | OIIIOIOI => fun (H:[+|C1 OIIIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 374
    | OIIIOIIO => fun (H:[+|C1 OIIIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 375
    | OIIIOIII => fun (H:[+|C1 OIIIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 376
    | OIIIIOOO => fun (H:[+|C1 OIIIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 377
    | OIIIIOOI => fun (H:[+|C1 OIIIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 378
    | OIIIIOIO => fun (H:[+|C1 OIIIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 379
    | OIIIIOII => fun (H:[+|C1 OIIIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 380
    | OIIIIIOO => fun (H:[+|C1 OIIIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 381
    | OIIIIIOI => fun (H:[+|C1 OIIIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 382
    | OIIIIIIO => fun (H:[+|C1 OIIIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 383
    | OIIIIIII => fun (H:[+|C1 OIIIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 384
    | IOOOOOOO => fun (H:[+|C1 IOOOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 385
    | IOOOOOOI => fun (H:[+|C1 IOOOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 386
    | IOOOOOIO => fun (H:[+|C1 IOOOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 387
    | IOOOOOII => fun (H:[+|C1 IOOOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 388
    | IOOOOIOO => fun (H:[+|C1 IOOOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 389
    | IOOOOIOI => fun (H:[+|C1 IOOOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 390
    | IOOOOIIO => fun (H:[+|C1 IOOOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 391
    | IOOOOIII => fun (H:[+|C1 IOOOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 392
    | IOOOIOOO => fun (H:[+|C1 IOOOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 393
    | IOOOIOOI => fun (H:[+|C1 IOOOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 394
    | IOOOIOIO => fun (H:[+|C1 IOOOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 395
    | IOOOIOII => fun (H:[+|C1 IOOOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 396
    | IOOOIIOO => fun (H:[+|C1 IOOOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 397
    | IOOOIIOI => fun (H:[+|C1 IOOOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 398
    | IOOOIIIO => fun (H:[+|C1 IOOOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 399
    | IOOOIIII => fun (H:[+|C1 IOOOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 400
    | IOOIOOOO => fun (H:[+|C1 IOOIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 401
    | IOOIOOOI => fun (H:[+|C1 IOOIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 402
    | IOOIOOIO => fun (H:[+|C1 IOOIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 403
    | IOOIOOII => fun (H:[+|C1 IOOIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 404
    | IOOIOIOO => fun (H:[+|C1 IOOIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 405
    | IOOIOIOI => fun (H:[+|C1 IOOIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 406
    | IOOIOIIO => fun (H:[+|C1 IOOIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 407
    | IOOIOIII => fun (H:[+|C1 IOOIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 408
    | IOOIIOOO => fun (H:[+|C1 IOOIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 409
    | IOOIIOOI => fun (H:[+|C1 IOOIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 410
    | IOOIIOIO => fun (H:[+|C1 IOOIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 411
    | IOOIIOII => fun (H:[+|C1 IOOIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 412
    | IOOIIIOO => fun (H:[+|C1 IOOIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 413
    | IOOIIIOI => fun (H:[+|C1 IOOIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 414
    | IOOIIIIO => fun (H:[+|C1 IOOIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 415
    | IOOIIIII => fun (H:[+|C1 IOOIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 416
    | IOIOOOOO => fun (H:[+|C1 IOIOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 417
    | IOIOOOOI => fun (H:[+|C1 IOIOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 418
    | IOIOOOIO => fun (H:[+|C1 IOIOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 419
    | IOIOOOII => fun (H:[+|C1 IOIOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 420
    | IOIOOIOO => fun (H:[+|C1 IOIOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 421
    | IOIOOIOI => fun (H:[+|C1 IOIOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 422
    | IOIOOIIO => fun (H:[+|C1 IOIOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 423
    | IOIOOIII => fun (H:[+|C1 IOIOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 424
    | IOIOIOOO => fun (H:[+|C1 IOIOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 425
    | IOIOIOOI => fun (H:[+|C1 IOIOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 426
    | IOIOIOIO => fun (H:[+|C1 IOIOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 427
    | IOIOIOII => fun (H:[+|C1 IOIOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 428
    | IOIOIIOO => fun (H:[+|C1 IOIOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 429
    | IOIOIIOI => fun (H:[+|C1 IOIOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 430
    | IOIOIIIO => fun (H:[+|C1 IOIOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 431
    | IOIOIIII => fun (H:[+|C1 IOIOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 432
    | IOIIOOOO => fun (H:[+|C1 IOIIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 433
    | IOIIOOOI => fun (H:[+|C1 IOIIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 434
    | IOIIOOIO => fun (H:[+|C1 IOIIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 435
    | IOIIOOII => fun (H:[+|C1 IOIIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 436
    | IOIIOIOO => fun (H:[+|C1 IOIIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 437
    | IOIIOIOI => fun (H:[+|C1 IOIIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 438
    | IOIIOIIO => fun (H:[+|C1 IOIIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 439
    | IOIIOIII => fun (H:[+|C1 IOIIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 440
    | IOIIIOOO => fun (H:[+|C1 IOIIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 441
    | IOIIIOOI => fun (H:[+|C1 IOIIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 442
    | IOIIIOIO => fun (H:[+|C1 IOIIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 443
    | IOIIIOII => fun (H:[+|C1 IOIIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 444
    | IOIIIIOO => fun (H:[+|C1 IOIIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 445
    | IOIIIIOI => fun (H:[+|C1 IOIIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 446
    | IOIIIIIO => fun (H:[+|C1 IOIIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 447
    | IOIIIIII => fun (H:[+|C1 IOIIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 448
    | IIOOOOOO => fun (H:[+|C1 IIOOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 449
    | IIOOOOOI => fun (H:[+|C1 IIOOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 450
    | IIOOOOIO => fun (H:[+|C1 IIOOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 451
    | IIOOOOII => fun (H:[+|C1 IIOOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 452
    | IIOOOIOO => fun (H:[+|C1 IIOOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 453
    | IIOOOIOI => fun (H:[+|C1 IIOOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 454
    | IIOOOIIO => fun (H:[+|C1 IIOOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 455
    | IIOOOIII => fun (H:[+|C1 IIOOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 456
    | IIOOIOOO => fun (H:[+|C1 IIOOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 457
    | IIOOIOOI => fun (H:[+|C1 IIOOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 458
    | IIOOIOIO => fun (H:[+|C1 IIOOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 459
    | IIOOIOII => fun (H:[+|C1 IIOOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 460
    | IIOOIIOO => fun (H:[+|C1 IIOOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 461
    | IIOOIIOI => fun (H:[+|C1 IIOOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 462
    | IIOOIIIO => fun (H:[+|C1 IIOOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 463
    | IIOOIIII => fun (H:[+|C1 IIOOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 464
    | IIOIOOOO => fun (H:[+|C1 IIOIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 465
    | IIOIOOOI => fun (H:[+|C1 IIOIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 466
    | IIOIOOIO => fun (H:[+|C1 IIOIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 467
    | IIOIOOII => fun (H:[+|C1 IIOIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 468
    | IIOIOIOO => fun (H:[+|C1 IIOIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 469
    | IIOIOIOI => fun (H:[+|C1 IIOIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 470
    | IIOIOIIO => fun (H:[+|C1 IIOIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 471
    | IIOIOIII => fun (H:[+|C1 IIOIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 472
    | IIOIIOOO => fun (H:[+|C1 IIOIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 473
    | IIOIIOOI => fun (H:[+|C1 IIOIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 474
    | IIOIIOIO => fun (H:[+|C1 IIOIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 475
    | IIOIIOII => fun (H:[+|C1 IIOIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 476
    | IIOIIIOO => fun (H:[+|C1 IIOIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 477
    | IIOIIIOI => fun (H:[+|C1 IIOIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 478
    | IIOIIIIO => fun (H:[+|C1 IIOIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 479
    | IIOIIIII => fun (H:[+|C1 IIOIIIII|] <= w8_B + (w8_B - 2)) => refl_equal 480
    | IIIOOOOO => fun (H:[+|C1 IIIOOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 481
    | IIIOOOOI => fun (H:[+|C1 IIIOOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 482
    | IIIOOOIO => fun (H:[+|C1 IIIOOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 483
    | IIIOOOII => fun (H:[+|C1 IIIOOOII|] <= w8_B + (w8_B - 2)) => refl_equal 484
    | IIIOOIOO => fun (H:[+|C1 IIIOOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 485
    | IIIOOIOI => fun (H:[+|C1 IIIOOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 486
    | IIIOOIIO => fun (H:[+|C1 IIIOOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 487
    | IIIOOIII => fun (H:[+|C1 IIIOOIII|] <= w8_B + (w8_B - 2)) => refl_equal 488
    | IIIOIOOO => fun (H:[+|C1 IIIOIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 489
    | IIIOIOOI => fun (H:[+|C1 IIIOIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 490
    | IIIOIOIO => fun (H:[+|C1 IIIOIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 491
    | IIIOIOII => fun (H:[+|C1 IIIOIOII|] <= w8_B + (w8_B - 2)) => refl_equal 492
    | IIIOIIOO => fun (H:[+|C1 IIIOIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 493
    | IIIOIIOI => fun (H:[+|C1 IIIOIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 494
    | IIIOIIIO => fun (H:[+|C1 IIIOIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 495
    | IIIOIIII => fun (H:[+|C1 IIIOIIII|] <= w8_B + (w8_B - 2)) => refl_equal 496
    | IIIIOOOO => fun (H:[+|C1 IIIIOOOO|] <= w8_B + (w8_B - 2)) => refl_equal 497
    | IIIIOOOI => fun (H:[+|C1 IIIIOOOI|] <= w8_B + (w8_B - 2)) => refl_equal 498
    | IIIIOOIO => fun (H:[+|C1 IIIIOOIO|] <= w8_B + (w8_B - 2)) => refl_equal 499
    | IIIIOOII => fun (H:[+|C1 IIIIOOII|] <= w8_B + (w8_B - 2)) => refl_equal 500
    | IIIIOIOO => fun (H:[+|C1 IIIIOIOO|] <= w8_B + (w8_B - 2)) => refl_equal 501
    | IIIIOIOI => fun (H:[+|C1 IIIIOIOI|] <= w8_B + (w8_B - 2)) => refl_equal 502
    | IIIIOIIO => fun (H:[+|C1 IIIIOIIO|] <= w8_B + (w8_B - 2)) => refl_equal 503
    | IIIIOIII => fun (H:[+|C1 IIIIOIII|] <= w8_B + (w8_B - 2)) => refl_equal 504
    | IIIIIOOO => fun (H:[+|C1 IIIIIOOO|] <= w8_B + (w8_B - 2)) => refl_equal 505
    | IIIIIOOI => fun (H:[+|C1 IIIIIOOI|] <= w8_B + (w8_B - 2)) => refl_equal 506
    | IIIIIOIO => fun (H:[+|C1 IIIIIOIO|] <= w8_B + (w8_B - 2)) => refl_equal 507
    | IIIIIOII => fun (H:[+|C1 IIIIIOII|] <= w8_B + (w8_B - 2)) => refl_equal 508
    | IIIIIIOO => fun (H:[+|C1 IIIIIIOO|] <= w8_B + (w8_B - 2)) => refl_equal 509
    | IIIIIIOI => fun (H:[+|C1 IIIIIIOI|] <= w8_B + (w8_B - 2)) => refl_equal 510
    | IIIIIIIO => fun (H:[+|C1 IIIIIIIO|] <= w8_B + (w8_B - 2)) => refl_equal 511
    | IIIIIIII =>
      fun (H:[+|C1 IIIIIIII|] <= w8_B + (w8_B - 2)) =>
        False_ind
          ([+|w8_carry_succ_c (C1 IIIIIIII)|] = [+|(C1 IIIIIIII)|] + 1)
          (H (refl_equal Gt))
    end
 end.

