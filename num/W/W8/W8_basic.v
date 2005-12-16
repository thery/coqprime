Require Import ZArith.
Require Export Basic_type.


Open Local Scope Z_scope.

Inductive w8 : Set :=
 | OOOOOOOO : w8
 | OOOOOOOI : w8
 | OOOOOOIO : w8
 | OOOOOOII : w8
 | OOOOOIOO : w8
 | OOOOOIOI : w8
 | OOOOOIIO : w8
 | OOOOOIII : w8
 | OOOOIOOO : w8
 | OOOOIOOI : w8
 | OOOOIOIO : w8
 | OOOOIOII : w8
 | OOOOIIOO : w8
 | OOOOIIOI : w8
 | OOOOIIIO : w8
 | OOOOIIII : w8
 | OOOIOOOO : w8
 | OOOIOOOI : w8
 | OOOIOOIO : w8
 | OOOIOOII : w8
 | OOOIOIOO : w8
 | OOOIOIOI : w8
 | OOOIOIIO : w8
 | OOOIOIII : w8
 | OOOIIOOO : w8
 | OOOIIOOI : w8
 | OOOIIOIO : w8
 | OOOIIOII : w8
 | OOOIIIOO : w8
 | OOOIIIOI : w8
 | OOOIIIIO : w8
 | OOOIIIII : w8
 | OOIOOOOO : w8
 | OOIOOOOI : w8
 | OOIOOOIO : w8
 | OOIOOOII : w8
 | OOIOOIOO : w8
 | OOIOOIOI : w8
 | OOIOOIIO : w8
 | OOIOOIII : w8
 | OOIOIOOO : w8
 | OOIOIOOI : w8
 | OOIOIOIO : w8
 | OOIOIOII : w8
 | OOIOIIOO : w8
 | OOIOIIOI : w8
 | OOIOIIIO : w8
 | OOIOIIII : w8
 | OOIIOOOO : w8
 | OOIIOOOI : w8
 | OOIIOOIO : w8
 | OOIIOOII : w8
 | OOIIOIOO : w8
 | OOIIOIOI : w8
 | OOIIOIIO : w8
 | OOIIOIII : w8
 | OOIIIOOO : w8
 | OOIIIOOI : w8
 | OOIIIOIO : w8
 | OOIIIOII : w8
 | OOIIIIOO : w8
 | OOIIIIOI : w8
 | OOIIIIIO : w8
 | OOIIIIII : w8
 | OIOOOOOO : w8
 | OIOOOOOI : w8
 | OIOOOOIO : w8
 | OIOOOOII : w8
 | OIOOOIOO : w8
 | OIOOOIOI : w8
 | OIOOOIIO : w8
 | OIOOOIII : w8
 | OIOOIOOO : w8
 | OIOOIOOI : w8
 | OIOOIOIO : w8
 | OIOOIOII : w8
 | OIOOIIOO : w8
 | OIOOIIOI : w8
 | OIOOIIIO : w8
 | OIOOIIII : w8
 | OIOIOOOO : w8
 | OIOIOOOI : w8
 | OIOIOOIO : w8
 | OIOIOOII : w8
 | OIOIOIOO : w8
 | OIOIOIOI : w8
 | OIOIOIIO : w8
 | OIOIOIII : w8
 | OIOIIOOO : w8
 | OIOIIOOI : w8
 | OIOIIOIO : w8
 | OIOIIOII : w8
 | OIOIIIOO : w8
 | OIOIIIOI : w8
 | OIOIIIIO : w8
 | OIOIIIII : w8
 | OIIOOOOO : w8
 | OIIOOOOI : w8
 | OIIOOOIO : w8
 | OIIOOOII : w8
 | OIIOOIOO : w8
 | OIIOOIOI : w8
 | OIIOOIIO : w8
 | OIIOOIII : w8
 | OIIOIOOO : w8
 | OIIOIOOI : w8
 | OIIOIOIO : w8
 | OIIOIOII : w8
 | OIIOIIOO : w8
 | OIIOIIOI : w8
 | OIIOIIIO : w8
 | OIIOIIII : w8
 | OIIIOOOO : w8
 | OIIIOOOI : w8
 | OIIIOOIO : w8
 | OIIIOOII : w8
 | OIIIOIOO : w8
 | OIIIOIOI : w8
 | OIIIOIIO : w8
 | OIIIOIII : w8
 | OIIIIOOO : w8
 | OIIIIOOI : w8
 | OIIIIOIO : w8
 | OIIIIOII : w8
 | OIIIIIOO : w8
 | OIIIIIOI : w8
 | OIIIIIIO : w8
 | OIIIIIII : w8
 | IOOOOOOO : w8
 | IOOOOOOI : w8
 | IOOOOOIO : w8
 | IOOOOOII : w8
 | IOOOOIOO : w8
 | IOOOOIOI : w8
 | IOOOOIIO : w8
 | IOOOOIII : w8
 | IOOOIOOO : w8
 | IOOOIOOI : w8
 | IOOOIOIO : w8
 | IOOOIOII : w8
 | IOOOIIOO : w8
 | IOOOIIOI : w8
 | IOOOIIIO : w8
 | IOOOIIII : w8
 | IOOIOOOO : w8
 | IOOIOOOI : w8
 | IOOIOOIO : w8
 | IOOIOOII : w8
 | IOOIOIOO : w8
 | IOOIOIOI : w8
 | IOOIOIIO : w8
 | IOOIOIII : w8
 | IOOIIOOO : w8
 | IOOIIOOI : w8
 | IOOIIOIO : w8
 | IOOIIOII : w8
 | IOOIIIOO : w8
 | IOOIIIOI : w8
 | IOOIIIIO : w8
 | IOOIIIII : w8
 | IOIOOOOO : w8
 | IOIOOOOI : w8
 | IOIOOOIO : w8
 | IOIOOOII : w8
 | IOIOOIOO : w8
 | IOIOOIOI : w8
 | IOIOOIIO : w8
 | IOIOOIII : w8
 | IOIOIOOO : w8
 | IOIOIOOI : w8
 | IOIOIOIO : w8
 | IOIOIOII : w8
 | IOIOIIOO : w8
 | IOIOIIOI : w8
 | IOIOIIIO : w8
 | IOIOIIII : w8
 | IOIIOOOO : w8
 | IOIIOOOI : w8
 | IOIIOOIO : w8
 | IOIIOOII : w8
 | IOIIOIOO : w8
 | IOIIOIOI : w8
 | IOIIOIIO : w8
 | IOIIOIII : w8
 | IOIIIOOO : w8
 | IOIIIOOI : w8
 | IOIIIOIO : w8
 | IOIIIOII : w8
 | IOIIIIOO : w8
 | IOIIIIOI : w8
 | IOIIIIIO : w8
 | IOIIIIII : w8
 | IIOOOOOO : w8
 | IIOOOOOI : w8
 | IIOOOOIO : w8
 | IIOOOOII : w8
 | IIOOOIOO : w8
 | IIOOOIOI : w8
 | IIOOOIIO : w8
 | IIOOOIII : w8
 | IIOOIOOO : w8
 | IIOOIOOI : w8
 | IIOOIOIO : w8
 | IIOOIOII : w8
 | IIOOIIOO : w8
 | IIOOIIOI : w8
 | IIOOIIIO : w8
 | IIOOIIII : w8
 | IIOIOOOO : w8
 | IIOIOOOI : w8
 | IIOIOOIO : w8
 | IIOIOOII : w8
 | IIOIOIOO : w8
 | IIOIOIOI : w8
 | IIOIOIIO : w8
 | IIOIOIII : w8
 | IIOIIOOO : w8
 | IIOIIOOI : w8
 | IIOIIOIO : w8
 | IIOIIOII : w8
 | IIOIIIOO : w8
 | IIOIIIOI : w8
 | IIOIIIIO : w8
 | IIOIIIII : w8
 | IIIOOOOO : w8
 | IIIOOOOI : w8
 | IIIOOOIO : w8
 | IIIOOOII : w8
 | IIIOOIOO : w8
 | IIIOOIOI : w8
 | IIIOOIIO : w8
 | IIIOOIII : w8
 | IIIOIOOO : w8
 | IIIOIOOI : w8
 | IIIOIOIO : w8
 | IIIOIOII : w8
 | IIIOIIOO : w8
 | IIIOIIOI : w8
 | IIIOIIIO : w8
 | IIIOIIII : w8
 | IIIIOOOO : w8
 | IIIIOOOI : w8
 | IIIIOOIO : w8
 | IIIIOOII : w8
 | IIIIOIOO : w8
 | IIIIOIOI : w8
 | IIIIOIIO : w8
 | IIIIOIII : w8
 | IIIIIOOO : w8
 | IIIIIOOI : w8
 | IIIIIOIO : w8
 | IIIIIOII : w8
 | IIIIIIOO : w8
 | IIIIIIOI : w8
 | IIIIIIIO : w8
 | IIIIIIII : w8.


(* ** Conversion functions with Z, N and positive ** *)

Definition w8_B := 256.
Definition w8_to_Z x :=
 match x with
 | OOOOOOOO => 0
 | OOOOOOOI => 1
 | OOOOOOIO => 2
 | OOOOOOII => 3
 | OOOOOIOO => 4
 | OOOOOIOI => 5
 | OOOOOIIO => 6
 | OOOOOIII => 7
 | OOOOIOOO => 8
 | OOOOIOOI => 9
 | OOOOIOIO => 10
 | OOOOIOII => 11
 | OOOOIIOO => 12
 | OOOOIIOI => 13
 | OOOOIIIO => 14
 | OOOOIIII => 15
 | OOOIOOOO => 16
 | OOOIOOOI => 17
 | OOOIOOIO => 18
 | OOOIOOII => 19
 | OOOIOIOO => 20
 | OOOIOIOI => 21
 | OOOIOIIO => 22
 | OOOIOIII => 23
 | OOOIIOOO => 24
 | OOOIIOOI => 25
 | OOOIIOIO => 26
 | OOOIIOII => 27
 | OOOIIIOO => 28
 | OOOIIIOI => 29
 | OOOIIIIO => 30
 | OOOIIIII => 31
 | OOIOOOOO => 32
 | OOIOOOOI => 33
 | OOIOOOIO => 34
 | OOIOOOII => 35
 | OOIOOIOO => 36
 | OOIOOIOI => 37
 | OOIOOIIO => 38
 | OOIOOIII => 39
 | OOIOIOOO => 40
 | OOIOIOOI => 41
 | OOIOIOIO => 42
 | OOIOIOII => 43
 | OOIOIIOO => 44
 | OOIOIIOI => 45
 | OOIOIIIO => 46
 | OOIOIIII => 47
 | OOIIOOOO => 48
 | OOIIOOOI => 49
 | OOIIOOIO => 50
 | OOIIOOII => 51
 | OOIIOIOO => 52
 | OOIIOIOI => 53
 | OOIIOIIO => 54
 | OOIIOIII => 55
 | OOIIIOOO => 56
 | OOIIIOOI => 57
 | OOIIIOIO => 58
 | OOIIIOII => 59
 | OOIIIIOO => 60
 | OOIIIIOI => 61
 | OOIIIIIO => 62
 | OOIIIIII => 63
 | OIOOOOOO => 64
 | OIOOOOOI => 65
 | OIOOOOIO => 66
 | OIOOOOII => 67
 | OIOOOIOO => 68
 | OIOOOIOI => 69
 | OIOOOIIO => 70
 | OIOOOIII => 71
 | OIOOIOOO => 72
 | OIOOIOOI => 73
 | OIOOIOIO => 74
 | OIOOIOII => 75
 | OIOOIIOO => 76
 | OIOOIIOI => 77
 | OIOOIIIO => 78
 | OIOOIIII => 79
 | OIOIOOOO => 80
 | OIOIOOOI => 81
 | OIOIOOIO => 82
 | OIOIOOII => 83
 | OIOIOIOO => 84
 | OIOIOIOI => 85
 | OIOIOIIO => 86
 | OIOIOIII => 87
 | OIOIIOOO => 88
 | OIOIIOOI => 89
 | OIOIIOIO => 90
 | OIOIIOII => 91
 | OIOIIIOO => 92
 | OIOIIIOI => 93
 | OIOIIIIO => 94
 | OIOIIIII => 95
 | OIIOOOOO => 96
 | OIIOOOOI => 97
 | OIIOOOIO => 98
 | OIIOOOII => 99
 | OIIOOIOO => 100
 | OIIOOIOI => 101
 | OIIOOIIO => 102
 | OIIOOIII => 103
 | OIIOIOOO => 104
 | OIIOIOOI => 105
 | OIIOIOIO => 106
 | OIIOIOII => 107
 | OIIOIIOO => 108
 | OIIOIIOI => 109
 | OIIOIIIO => 110
 | OIIOIIII => 111
 | OIIIOOOO => 112
 | OIIIOOOI => 113
 | OIIIOOIO => 114
 | OIIIOOII => 115
 | OIIIOIOO => 116
 | OIIIOIOI => 117
 | OIIIOIIO => 118
 | OIIIOIII => 119
 | OIIIIOOO => 120
 | OIIIIOOI => 121
 | OIIIIOIO => 122
 | OIIIIOII => 123
 | OIIIIIOO => 124
 | OIIIIIOI => 125
 | OIIIIIIO => 126
 | OIIIIIII => 127
 | IOOOOOOO => 128
 | IOOOOOOI => 129
 | IOOOOOIO => 130
 | IOOOOOII => 131
 | IOOOOIOO => 132
 | IOOOOIOI => 133
 | IOOOOIIO => 134
 | IOOOOIII => 135
 | IOOOIOOO => 136
 | IOOOIOOI => 137
 | IOOOIOIO => 138
 | IOOOIOII => 139
 | IOOOIIOO => 140
 | IOOOIIOI => 141
 | IOOOIIIO => 142
 | IOOOIIII => 143
 | IOOIOOOO => 144
 | IOOIOOOI => 145
 | IOOIOOIO => 146
 | IOOIOOII => 147
 | IOOIOIOO => 148
 | IOOIOIOI => 149
 | IOOIOIIO => 150
 | IOOIOIII => 151
 | IOOIIOOO => 152
 | IOOIIOOI => 153
 | IOOIIOIO => 154
 | IOOIIOII => 155
 | IOOIIIOO => 156
 | IOOIIIOI => 157
 | IOOIIIIO => 158
 | IOOIIIII => 159
 | IOIOOOOO => 160
 | IOIOOOOI => 161
 | IOIOOOIO => 162
 | IOIOOOII => 163
 | IOIOOIOO => 164
 | IOIOOIOI => 165
 | IOIOOIIO => 166
 | IOIOOIII => 167
 | IOIOIOOO => 168
 | IOIOIOOI => 169
 | IOIOIOIO => 170
 | IOIOIOII => 171
 | IOIOIIOO => 172
 | IOIOIIOI => 173
 | IOIOIIIO => 174
 | IOIOIIII => 175
 | IOIIOOOO => 176
 | IOIIOOOI => 177
 | IOIIOOIO => 178
 | IOIIOOII => 179
 | IOIIOIOO => 180
 | IOIIOIOI => 181
 | IOIIOIIO => 182
 | IOIIOIII => 183
 | IOIIIOOO => 184
 | IOIIIOOI => 185
 | IOIIIOIO => 186
 | IOIIIOII => 187
 | IOIIIIOO => 188
 | IOIIIIOI => 189
 | IOIIIIIO => 190
 | IOIIIIII => 191
 | IIOOOOOO => 192
 | IIOOOOOI => 193
 | IIOOOOIO => 194
 | IIOOOOII => 195
 | IIOOOIOO => 196
 | IIOOOIOI => 197
 | IIOOOIIO => 198
 | IIOOOIII => 199
 | IIOOIOOO => 200
 | IIOOIOOI => 201
 | IIOOIOIO => 202
 | IIOOIOII => 203
 | IIOOIIOO => 204
 | IIOOIIOI => 205
 | IIOOIIIO => 206
 | IIOOIIII => 207
 | IIOIOOOO => 208
 | IIOIOOOI => 209
 | IIOIOOIO => 210
 | IIOIOOII => 211
 | IIOIOIOO => 212
 | IIOIOIOI => 213
 | IIOIOIIO => 214
 | IIOIOIII => 215
 | IIOIIOOO => 216
 | IIOIIOOI => 217
 | IIOIIOIO => 218
 | IIOIIOII => 219
 | IIOIIIOO => 220
 | IIOIIIOI => 221
 | IIOIIIIO => 222
 | IIOIIIII => 223
 | IIIOOOOO => 224
 | IIIOOOOI => 225
 | IIIOOOIO => 226
 | IIIOOOII => 227
 | IIIOOIOO => 228
 | IIIOOIOI => 229
 | IIIOOIIO => 230
 | IIIOOIII => 231
 | IIIOIOOO => 232
 | IIIOIOOI => 233
 | IIIOIOIO => 234
 | IIIOIOII => 235
 | IIIOIIOO => 236
 | IIIOIIOI => 237
 | IIIOIIIO => 238
 | IIIOIIII => 239
 | IIIIOOOO => 240
 | IIIIOOOI => 241
 | IIIIOOIO => 242
 | IIIIOOII => 243
 | IIIIOIOO => 244
 | IIIIOIOI => 245
 | IIIIOIIO => 246
 | IIIIOIII => 247
 | IIIIIOOO => 248
 | IIIIIOOI => 249
 | IIIIIOIO => 250
 | IIIIIOII => 251
 | IIIIIIOO => 252
 | IIIIIIOI => 253
 | IIIIIIIO => 254
 | IIIIIIII => 255
 end.

Definition w8_of_pos p :=
 match p with
 | xH => (N0, OOOOOOOI)
 | (xO xH) => (N0, OOOOOOIO)
 | (xI xH) => (N0, OOOOOOII)
 | (xO (xO xH)) => (N0, OOOOOIOO)
 | (xI (xO xH)) => (N0, OOOOOIOI)
 | (xO (xI xH)) => (N0, OOOOOIIO)
 | (xI (xI xH)) => (N0, OOOOOIII)
 | (xO (xO (xO xH))) => (N0, OOOOIOOO)
 | (xI (xO (xO xH))) => (N0, OOOOIOOI)
 | (xO (xI (xO xH))) => (N0, OOOOIOIO)
 | (xI (xI (xO xH))) => (N0, OOOOIOII)
 | (xO (xO (xI xH))) => (N0, OOOOIIOO)
 | (xI (xO (xI xH))) => (N0, OOOOIIOI)
 | (xO (xI (xI xH))) => (N0, OOOOIIIO)
 | (xI (xI (xI xH))) => (N0, OOOOIIII)
 | (xO (xO (xO (xO xH)))) => (N0, OOOIOOOO)
 | (xI (xO (xO (xO xH)))) => (N0, OOOIOOOI)
 | (xO (xI (xO (xO xH)))) => (N0, OOOIOOIO)
 | (xI (xI (xO (xO xH)))) => (N0, OOOIOOII)
 | (xO (xO (xI (xO xH)))) => (N0, OOOIOIOO)
 | (xI (xO (xI (xO xH)))) => (N0, OOOIOIOI)
 | (xO (xI (xI (xO xH)))) => (N0, OOOIOIIO)
 | (xI (xI (xI (xO xH)))) => (N0, OOOIOIII)
 | (xO (xO (xO (xI xH)))) => (N0, OOOIIOOO)
 | (xI (xO (xO (xI xH)))) => (N0, OOOIIOOI)
 | (xO (xI (xO (xI xH)))) => (N0, OOOIIOIO)
 | (xI (xI (xO (xI xH)))) => (N0, OOOIIOII)
 | (xO (xO (xI (xI xH)))) => (N0, OOOIIIOO)
 | (xI (xO (xI (xI xH)))) => (N0, OOOIIIOI)
 | (xO (xI (xI (xI xH)))) => (N0, OOOIIIIO)
 | (xI (xI (xI (xI xH)))) => (N0, OOOIIIII)
 | (xO (xO (xO (xO (xO xH))))) => (N0, OOIOOOOO)
 | (xI (xO (xO (xO (xO xH))))) => (N0, OOIOOOOI)
 | (xO (xI (xO (xO (xO xH))))) => (N0, OOIOOOIO)
 | (xI (xI (xO (xO (xO xH))))) => (N0, OOIOOOII)
 | (xO (xO (xI (xO (xO xH))))) => (N0, OOIOOIOO)
 | (xI (xO (xI (xO (xO xH))))) => (N0, OOIOOIOI)
 | (xO (xI (xI (xO (xO xH))))) => (N0, OOIOOIIO)
 | (xI (xI (xI (xO (xO xH))))) => (N0, OOIOOIII)
 | (xO (xO (xO (xI (xO xH))))) => (N0, OOIOIOOO)
 | (xI (xO (xO (xI (xO xH))))) => (N0, OOIOIOOI)
 | (xO (xI (xO (xI (xO xH))))) => (N0, OOIOIOIO)
 | (xI (xI (xO (xI (xO xH))))) => (N0, OOIOIOII)
 | (xO (xO (xI (xI (xO xH))))) => (N0, OOIOIIOO)
 | (xI (xO (xI (xI (xO xH))))) => (N0, OOIOIIOI)
 | (xO (xI (xI (xI (xO xH))))) => (N0, OOIOIIIO)
 | (xI (xI (xI (xI (xO xH))))) => (N0, OOIOIIII)
 | (xO (xO (xO (xO (xI xH))))) => (N0, OOIIOOOO)
 | (xI (xO (xO (xO (xI xH))))) => (N0, OOIIOOOI)
 | (xO (xI (xO (xO (xI xH))))) => (N0, OOIIOOIO)
 | (xI (xI (xO (xO (xI xH))))) => (N0, OOIIOOII)
 | (xO (xO (xI (xO (xI xH))))) => (N0, OOIIOIOO)
 | (xI (xO (xI (xO (xI xH))))) => (N0, OOIIOIOI)
 | (xO (xI (xI (xO (xI xH))))) => (N0, OOIIOIIO)
 | (xI (xI (xI (xO (xI xH))))) => (N0, OOIIOIII)
 | (xO (xO (xO (xI (xI xH))))) => (N0, OOIIIOOO)
 | (xI (xO (xO (xI (xI xH))))) => (N0, OOIIIOOI)
 | (xO (xI (xO (xI (xI xH))))) => (N0, OOIIIOIO)
 | (xI (xI (xO (xI (xI xH))))) => (N0, OOIIIOII)
 | (xO (xO (xI (xI (xI xH))))) => (N0, OOIIIIOO)
 | (xI (xO (xI (xI (xI xH))))) => (N0, OOIIIIOI)
 | (xO (xI (xI (xI (xI xH))))) => (N0, OOIIIIIO)
 | (xI (xI (xI (xI (xI xH))))) => (N0, OOIIIIII)
 | (xO (xO (xO (xO (xO (xO xH)))))) => (N0, OIOOOOOO)
 | (xI (xO (xO (xO (xO (xO xH)))))) => (N0, OIOOOOOI)
 | (xO (xI (xO (xO (xO (xO xH)))))) => (N0, OIOOOOIO)
 | (xI (xI (xO (xO (xO (xO xH)))))) => (N0, OIOOOOII)
 | (xO (xO (xI (xO (xO (xO xH)))))) => (N0, OIOOOIOO)
 | (xI (xO (xI (xO (xO (xO xH)))))) => (N0, OIOOOIOI)
 | (xO (xI (xI (xO (xO (xO xH)))))) => (N0, OIOOOIIO)
 | (xI (xI (xI (xO (xO (xO xH)))))) => (N0, OIOOOIII)
 | (xO (xO (xO (xI (xO (xO xH)))))) => (N0, OIOOIOOO)
 | (xI (xO (xO (xI (xO (xO xH)))))) => (N0, OIOOIOOI)
 | (xO (xI (xO (xI (xO (xO xH)))))) => (N0, OIOOIOIO)
 | (xI (xI (xO (xI (xO (xO xH)))))) => (N0, OIOOIOII)
 | (xO (xO (xI (xI (xO (xO xH)))))) => (N0, OIOOIIOO)
 | (xI (xO (xI (xI (xO (xO xH)))))) => (N0, OIOOIIOI)
 | (xO (xI (xI (xI (xO (xO xH)))))) => (N0, OIOOIIIO)
 | (xI (xI (xI (xI (xO (xO xH)))))) => (N0, OIOOIIII)
 | (xO (xO (xO (xO (xI (xO xH)))))) => (N0, OIOIOOOO)
 | (xI (xO (xO (xO (xI (xO xH)))))) => (N0, OIOIOOOI)
 | (xO (xI (xO (xO (xI (xO xH)))))) => (N0, OIOIOOIO)
 | (xI (xI (xO (xO (xI (xO xH)))))) => (N0, OIOIOOII)
 | (xO (xO (xI (xO (xI (xO xH)))))) => (N0, OIOIOIOO)
 | (xI (xO (xI (xO (xI (xO xH)))))) => (N0, OIOIOIOI)
 | (xO (xI (xI (xO (xI (xO xH)))))) => (N0, OIOIOIIO)
 | (xI (xI (xI (xO (xI (xO xH)))))) => (N0, OIOIOIII)
 | (xO (xO (xO (xI (xI (xO xH)))))) => (N0, OIOIIOOO)
 | (xI (xO (xO (xI (xI (xO xH)))))) => (N0, OIOIIOOI)
 | (xO (xI (xO (xI (xI (xO xH)))))) => (N0, OIOIIOIO)
 | (xI (xI (xO (xI (xI (xO xH)))))) => (N0, OIOIIOII)
 | (xO (xO (xI (xI (xI (xO xH)))))) => (N0, OIOIIIOO)
 | (xI (xO (xI (xI (xI (xO xH)))))) => (N0, OIOIIIOI)
 | (xO (xI (xI (xI (xI (xO xH)))))) => (N0, OIOIIIIO)
 | (xI (xI (xI (xI (xI (xO xH)))))) => (N0, OIOIIIII)
 | (xO (xO (xO (xO (xO (xI xH)))))) => (N0, OIIOOOOO)
 | (xI (xO (xO (xO (xO (xI xH)))))) => (N0, OIIOOOOI)
 | (xO (xI (xO (xO (xO (xI xH)))))) => (N0, OIIOOOIO)
 | (xI (xI (xO (xO (xO (xI xH)))))) => (N0, OIIOOOII)
 | (xO (xO (xI (xO (xO (xI xH)))))) => (N0, OIIOOIOO)
 | (xI (xO (xI (xO (xO (xI xH)))))) => (N0, OIIOOIOI)
 | (xO (xI (xI (xO (xO (xI xH)))))) => (N0, OIIOOIIO)
 | (xI (xI (xI (xO (xO (xI xH)))))) => (N0, OIIOOIII)
 | (xO (xO (xO (xI (xO (xI xH)))))) => (N0, OIIOIOOO)
 | (xI (xO (xO (xI (xO (xI xH)))))) => (N0, OIIOIOOI)
 | (xO (xI (xO (xI (xO (xI xH)))))) => (N0, OIIOIOIO)
 | (xI (xI (xO (xI (xO (xI xH)))))) => (N0, OIIOIOII)
 | (xO (xO (xI (xI (xO (xI xH)))))) => (N0, OIIOIIOO)
 | (xI (xO (xI (xI (xO (xI xH)))))) => (N0, OIIOIIOI)
 | (xO (xI (xI (xI (xO (xI xH)))))) => (N0, OIIOIIIO)
 | (xI (xI (xI (xI (xO (xI xH)))))) => (N0, OIIOIIII)
 | (xO (xO (xO (xO (xI (xI xH)))))) => (N0, OIIIOOOO)
 | (xI (xO (xO (xO (xI (xI xH)))))) => (N0, OIIIOOOI)
 | (xO (xI (xO (xO (xI (xI xH)))))) => (N0, OIIIOOIO)
 | (xI (xI (xO (xO (xI (xI xH)))))) => (N0, OIIIOOII)
 | (xO (xO (xI (xO (xI (xI xH)))))) => (N0, OIIIOIOO)
 | (xI (xO (xI (xO (xI (xI xH)))))) => (N0, OIIIOIOI)
 | (xO (xI (xI (xO (xI (xI xH)))))) => (N0, OIIIOIIO)
 | (xI (xI (xI (xO (xI (xI xH)))))) => (N0, OIIIOIII)
 | (xO (xO (xO (xI (xI (xI xH)))))) => (N0, OIIIIOOO)
 | (xI (xO (xO (xI (xI (xI xH)))))) => (N0, OIIIIOOI)
 | (xO (xI (xO (xI (xI (xI xH)))))) => (N0, OIIIIOIO)
 | (xI (xI (xO (xI (xI (xI xH)))))) => (N0, OIIIIOII)
 | (xO (xO (xI (xI (xI (xI xH)))))) => (N0, OIIIIIOO)
 | (xI (xO (xI (xI (xI (xI xH)))))) => (N0, OIIIIIOI)
 | (xO (xI (xI (xI (xI (xI xH)))))) => (N0, OIIIIIIO)
 | (xI (xI (xI (xI (xI (xI xH)))))) => (N0, OIIIIIII)
 | (xO (xO (xO (xO (xO (xO (xO xH))))))) => (N0, IOOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xO xH))))))) => (N0, IOOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xO xH))))))) => (N0, IOOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xO xH))))))) => (N0, IOOOOOII)
 | (xO (xO (xI (xO (xO (xO (xO xH))))))) => (N0, IOOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xO xH))))))) => (N0, IOOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xO xH))))))) => (N0, IOOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xO xH))))))) => (N0, IOOOOIII)
 | (xO (xO (xO (xI (xO (xO (xO xH))))))) => (N0, IOOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xO xH))))))) => (N0, IOOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xO xH))))))) => (N0, IOOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xO xH))))))) => (N0, IOOOIOII)
 | (xO (xO (xI (xI (xO (xO (xO xH))))))) => (N0, IOOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xO xH))))))) => (N0, IOOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xO xH))))))) => (N0, IOOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xO xH))))))) => (N0, IOOOIIII)
 | (xO (xO (xO (xO (xI (xO (xO xH))))))) => (N0, IOOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xO xH))))))) => (N0, IOOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xO xH))))))) => (N0, IOOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xO xH))))))) => (N0, IOOIOOII)
 | (xO (xO (xI (xO (xI (xO (xO xH))))))) => (N0, IOOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xO xH))))))) => (N0, IOOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xO xH))))))) => (N0, IOOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xO xH))))))) => (N0, IOOIOIII)
 | (xO (xO (xO (xI (xI (xO (xO xH))))))) => (N0, IOOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xO xH))))))) => (N0, IOOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xO xH))))))) => (N0, IOOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xO xH))))))) => (N0, IOOIIOII)
 | (xO (xO (xI (xI (xI (xO (xO xH))))))) => (N0, IOOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xO xH))))))) => (N0, IOOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xO xH))))))) => (N0, IOOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xO xH))))))) => (N0, IOOIIIII)
 | (xO (xO (xO (xO (xO (xI (xO xH))))))) => (N0, IOIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xO xH))))))) => (N0, IOIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xO xH))))))) => (N0, IOIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xO xH))))))) => (N0, IOIOOOII)
 | (xO (xO (xI (xO (xO (xI (xO xH))))))) => (N0, IOIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xO xH))))))) => (N0, IOIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xO xH))))))) => (N0, IOIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xO xH))))))) => (N0, IOIOOIII)
 | (xO (xO (xO (xI (xO (xI (xO xH))))))) => (N0, IOIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xO xH))))))) => (N0, IOIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xO xH))))))) => (N0, IOIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xO xH))))))) => (N0, IOIOIOII)
 | (xO (xO (xI (xI (xO (xI (xO xH))))))) => (N0, IOIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xO xH))))))) => (N0, IOIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xO xH))))))) => (N0, IOIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xO xH))))))) => (N0, IOIOIIII)
 | (xO (xO (xO (xO (xI (xI (xO xH))))))) => (N0, IOIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xO xH))))))) => (N0, IOIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xO xH))))))) => (N0, IOIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xO xH))))))) => (N0, IOIIOOII)
 | (xO (xO (xI (xO (xI (xI (xO xH))))))) => (N0, IOIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xO xH))))))) => (N0, IOIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xO xH))))))) => (N0, IOIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xO xH))))))) => (N0, IOIIOIII)
 | (xO (xO (xO (xI (xI (xI (xO xH))))))) => (N0, IOIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xO xH))))))) => (N0, IOIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xO xH))))))) => (N0, IOIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xO xH))))))) => (N0, IOIIIOII)
 | (xO (xO (xI (xI (xI (xI (xO xH))))))) => (N0, IOIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xO xH))))))) => (N0, IOIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xO xH))))))) => (N0, IOIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xO xH))))))) => (N0, IOIIIIII)
 | (xO (xO (xO (xO (xO (xO (xI xH))))))) => (N0, IIOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xI xH))))))) => (N0, IIOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xI xH))))))) => (N0, IIOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xI xH))))))) => (N0, IIOOOOII)
 | (xO (xO (xI (xO (xO (xO (xI xH))))))) => (N0, IIOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xI xH))))))) => (N0, IIOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xI xH))))))) => (N0, IIOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xI xH))))))) => (N0, IIOOOIII)
 | (xO (xO (xO (xI (xO (xO (xI xH))))))) => (N0, IIOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xI xH))))))) => (N0, IIOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xI xH))))))) => (N0, IIOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xI xH))))))) => (N0, IIOOIOII)
 | (xO (xO (xI (xI (xO (xO (xI xH))))))) => (N0, IIOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xI xH))))))) => (N0, IIOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xI xH))))))) => (N0, IIOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xI xH))))))) => (N0, IIOOIIII)
 | (xO (xO (xO (xO (xI (xO (xI xH))))))) => (N0, IIOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xI xH))))))) => (N0, IIOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xI xH))))))) => (N0, IIOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xI xH))))))) => (N0, IIOIOOII)
 | (xO (xO (xI (xO (xI (xO (xI xH))))))) => (N0, IIOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xI xH))))))) => (N0, IIOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xI xH))))))) => (N0, IIOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xI xH))))))) => (N0, IIOIOIII)
 | (xO (xO (xO (xI (xI (xO (xI xH))))))) => (N0, IIOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xI xH))))))) => (N0, IIOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xI xH))))))) => (N0, IIOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xI xH))))))) => (N0, IIOIIOII)
 | (xO (xO (xI (xI (xI (xO (xI xH))))))) => (N0, IIOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xI xH))))))) => (N0, IIOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xI xH))))))) => (N0, IIOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xI xH))))))) => (N0, IIOIIIII)
 | (xO (xO (xO (xO (xO (xI (xI xH))))))) => (N0, IIIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xI xH))))))) => (N0, IIIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xI xH))))))) => (N0, IIIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xI xH))))))) => (N0, IIIOOOII)
 | (xO (xO (xI (xO (xO (xI (xI xH))))))) => (N0, IIIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xI xH))))))) => (N0, IIIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xI xH))))))) => (N0, IIIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xI xH))))))) => (N0, IIIOOIII)
 | (xO (xO (xO (xI (xO (xI (xI xH))))))) => (N0, IIIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xI xH))))))) => (N0, IIIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xI xH))))))) => (N0, IIIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xI xH))))))) => (N0, IIIOIOII)
 | (xO (xO (xI (xI (xO (xI (xI xH))))))) => (N0, IIIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xI xH))))))) => (N0, IIIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xI xH))))))) => (N0, IIIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xI xH))))))) => (N0, IIIOIIII)
 | (xO (xO (xO (xO (xI (xI (xI xH))))))) => (N0, IIIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xI xH))))))) => (N0, IIIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xI xH))))))) => (N0, IIIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xI xH))))))) => (N0, IIIIOOII)
 | (xO (xO (xI (xO (xI (xI (xI xH))))))) => (N0, IIIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xI xH))))))) => (N0, IIIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xI xH))))))) => (N0, IIIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xI xH))))))) => (N0, IIIIOIII)
 | (xO (xO (xO (xI (xI (xI (xI xH))))))) => (N0, IIIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xI xH))))))) => (N0, IIIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xI xH))))))) => (N0, IIIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xI xH))))))) => (N0, IIIIIOII)
 | (xO (xO (xI (xI (xI (xI (xI xH))))))) => (N0, IIIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xI xH))))))) => (N0, IIIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xI xH))))))) => (N0, IIIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xI xH))))))) => (N0, IIIIIIII)
 | (xO (xO (xO (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOOII)
 | (xO (xO (xI (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xO (xO p)))))))) => (Npos p, OOOOOIII)
 | (xO (xO (xO (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIOII)
 | (xO (xO (xI (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xO (xO p)))))))) => (Npos p, OOOOIIII)
 | (xO (xO (xO (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOOII)
 | (xO (xO (xI (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xO (xO p)))))))) => (Npos p, OOOIOIII)
 | (xO (xO (xO (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIOII)
 | (xO (xO (xI (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xO (xO p)))))))) => (Npos p, OOOIIIII)
 | (xO (xO (xO (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOOII)
 | (xO (xO (xI (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xO (xO p)))))))) => (Npos p, OOIOOIII)
 | (xO (xO (xO (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIOII)
 | (xO (xO (xI (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xO (xO p)))))))) => (Npos p, OOIOIIII)
 | (xO (xO (xO (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOOII)
 | (xO (xO (xI (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xO (xO p)))))))) => (Npos p, OOIIOIII)
 | (xO (xO (xO (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIOII)
 | (xO (xO (xI (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xO (xO p)))))))) => (Npos p, OOIIIIII)
 | (xO (xO (xO (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOOII)
 | (xO (xO (xI (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xI (xO p)))))))) => (Npos p, OIOOOIII)
 | (xO (xO (xO (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIOII)
 | (xO (xO (xI (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xI (xO p)))))))) => (Npos p, OIOOIIII)
 | (xO (xO (xO (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOOII)
 | (xO (xO (xI (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xI (xO p)))))))) => (Npos p, OIOIOIII)
 | (xO (xO (xO (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIOII)
 | (xO (xO (xI (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xI (xO p)))))))) => (Npos p, OIOIIIII)
 | (xO (xO (xO (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOOII)
 | (xO (xO (xI (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xI (xO p)))))))) => (Npos p, OIIOOIII)
 | (xO (xO (xO (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIOII)
 | (xO (xO (xI (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xI (xO p)))))))) => (Npos p, OIIOIIII)
 | (xO (xO (xO (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOOII)
 | (xO (xO (xI (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xI (xO p)))))))) => (Npos p, OIIIOIII)
 | (xO (xO (xO (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIOII)
 | (xO (xO (xI (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xI (xO p)))))))) => (Npos p, OIIIIIII)
 | (xO (xO (xO (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOOII)
 | (xO (xO (xI (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xO (xI p)))))))) => (Npos p, IOOOOIII)
 | (xO (xO (xO (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIOII)
 | (xO (xO (xI (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xO (xI p)))))))) => (Npos p, IOOOIIII)
 | (xO (xO (xO (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOOII)
 | (xO (xO (xI (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xO (xI p)))))))) => (Npos p, IOOIOIII)
 | (xO (xO (xO (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIOII)
 | (xO (xO (xI (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xO (xI p)))))))) => (Npos p, IOOIIIII)
 | (xO (xO (xO (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOOII)
 | (xO (xO (xI (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xO (xI p)))))))) => (Npos p, IOIOOIII)
 | (xO (xO (xO (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIOII)
 | (xO (xO (xI (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xO (xI p)))))))) => (Npos p, IOIOIIII)
 | (xO (xO (xO (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOOII)
 | (xO (xO (xI (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xO (xI p)))))))) => (Npos p, IOIIOIII)
 | (xO (xO (xO (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIOII)
 | (xO (xO (xI (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xO (xI p)))))))) => (Npos p, IOIIIIII)
 | (xO (xO (xO (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOOOO)
 | (xI (xO (xO (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOOOI)
 | (xO (xI (xO (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOOIO)
 | (xI (xI (xO (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOOII)
 | (xO (xO (xI (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOIOO)
 | (xI (xO (xI (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOIOI)
 | (xO (xI (xI (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOIIO)
 | (xI (xI (xI (xO (xO (xO (xI (xI p)))))))) => (Npos p, IIOOOIII)
 | (xO (xO (xO (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIOOO)
 | (xI (xO (xO (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIOOI)
 | (xO (xI (xO (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIOIO)
 | (xI (xI (xO (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIOII)
 | (xO (xO (xI (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIIOO)
 | (xI (xO (xI (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIIOI)
 | (xO (xI (xI (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIIIO)
 | (xI (xI (xI (xI (xO (xO (xI (xI p)))))))) => (Npos p, IIOOIIII)
 | (xO (xO (xO (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOOOO)
 | (xI (xO (xO (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOOOI)
 | (xO (xI (xO (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOOIO)
 | (xI (xI (xO (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOOII)
 | (xO (xO (xI (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOIOO)
 | (xI (xO (xI (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOIOI)
 | (xO (xI (xI (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOIIO)
 | (xI (xI (xI (xO (xI (xO (xI (xI p)))))))) => (Npos p, IIOIOIII)
 | (xO (xO (xO (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIOOO)
 | (xI (xO (xO (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIOOI)
 | (xO (xI (xO (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIOIO)
 | (xI (xI (xO (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIOII)
 | (xO (xO (xI (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIIOO)
 | (xI (xO (xI (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIIOI)
 | (xO (xI (xI (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIIIO)
 | (xI (xI (xI (xI (xI (xO (xI (xI p)))))))) => (Npos p, IIOIIIII)
 | (xO (xO (xO (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOOOO)
 | (xI (xO (xO (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOOOI)
 | (xO (xI (xO (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOOIO)
 | (xI (xI (xO (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOOII)
 | (xO (xO (xI (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOIOO)
 | (xI (xO (xI (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOIOI)
 | (xO (xI (xI (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOIIO)
 | (xI (xI (xI (xO (xO (xI (xI (xI p)))))))) => (Npos p, IIIOOIII)
 | (xO (xO (xO (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIOOO)
 | (xI (xO (xO (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIOOI)
 | (xO (xI (xO (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIOIO)
 | (xI (xI (xO (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIOII)
 | (xO (xO (xI (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIIOO)
 | (xI (xO (xI (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIIOI)
 | (xO (xI (xI (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIIIO)
 | (xI (xI (xI (xI (xO (xI (xI (xI p)))))))) => (Npos p, IIIOIIII)
 | (xO (xO (xO (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOOOO)
 | (xI (xO (xO (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOOOI)
 | (xO (xI (xO (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOOIO)
 | (xI (xI (xO (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOOII)
 | (xO (xO (xI (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOIOO)
 | (xI (xO (xI (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOIOI)
 | (xO (xI (xI (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOIIO)
 | (xI (xI (xI (xO (xI (xI (xI (xI p)))))))) => (Npos p, IIIIOIII)
 | (xO (xO (xO (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIOOO)
 | (xI (xO (xO (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIOOI)
 | (xO (xI (xO (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIOIO)
 | (xI (xI (xO (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIOII)
 | (xO (xO (xI (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIIOO)
 | (xI (xO (xI (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIIOI)
 | (xO (xI (xI (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIIIO)
 | (xI (xI (xI (xI (xI (xI (xI (xI p)))))))) => (Npos p, IIIIIIII)
 end.

Definition w8_of_N n :=
 match n with
 | N0 => (N0, OOOOOOOO)
 | Npos p => w8_of_pos p
 end.


(* ** Constructors for the next level ** *)

Definition w8_WW xh xl :=
 match xh, xl with
 | OOOOOOOO, OOOOOOOO => W0
 | _, _ => WW xh xl
end.

Definition w8_CW ch xl :=
Eval compute in
 match ch with
 | C0 xh => C0 (w8_WW xh xl)
 | C1 xh => C1 (w8_WW xh xl)
 end.

Notation "[| x |]" := (w8_to_Z x)  (at level 0, x at level 99) : w8_scope.
Notation "[+| x |]" := (interp_carry 1 w8_B w8_to_Z x)  (at level 0, x at level 99) : w8_scope.
Notation "[-| x |]" := (interp_carry (-1) w8_B w8_to_Z x)  (at level 0, x at level 99) : w8_scope.
Notation "[|| x ||]" := (zn2z_to_Z w8_B w8_to_Z x)  (at level 0, x at level 99) : w8_scope.
