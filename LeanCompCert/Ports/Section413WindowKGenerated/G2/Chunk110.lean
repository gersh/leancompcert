import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk110

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360794197802866660, 360794198467343117⟩, ⟨(-2296067599726995797), (-2296062646214467129)⟩, true⟩

def state01 : KState := ⟨⟨360695479912648634, 360695480578398313⟩, ⟨(-1210436907254891964), (-1210431939730480404)⟩, true⟩

def words00 : List Nat := [360585498352692353, 360585504057421481, 360585517980584259, 360585531901257962, 360585541753972383, 360585543435906873, 360585543436027329, 360585540918971602, 360585541255836294, 360585551240487998]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360466501188490496, 360466501855504348⟩, ⟨1311401167218614516, 1311406148667933414⟩, true⟩

def words01 : List Nat := [360585555060833162, 360585558880506955, 360585558880626383, 360585558548696393, 360585550054795066, 360585539390639837, 360585528728380087, 360585521688875970, 360585515027946114, 360585504228341729]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360688504926028215, 360688505594307669⟩, ⟨(-1136069349917118038), (-1136064354514729182)⟩, true⟩

def words02 : List Nat := [360585493430666815, 360585489029205874, 360585495307535815, 360585501584752935, 360585501584879923, 360585500080387942, 360585497765499977, 360585500696663243, 360585507919235570, 360585517256485647]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360442317730022697, 360442318399582412⟩, ⟨1580910409051209753, 1580915418581271839⟩, true⟩

def words03 : List Nat := [360585522467752955, 360585527678092487, 360585529069544720, 360585534703081349, 360585538183424603, 360585541663159101, 360585541663279343, 360585540009254418, 360585530231894420, 360585517259961151]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360500856150912327, 360500856821738096⟩, ⟨933861431744212643, 933866455257793833⟩, true⟩

def words04 : List Nat := [360585504290333602, 360585496539076763, 360585480668512439, 360585460586650633, 360585440508402596, 360585417366291114, 360585400635871822, 360585392055818097, 360585383477302961, 360585369623118892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360609517254528872, 360609517926625953⟩, ⟨(-268001322657389885), (-267996285089503621)⟩, true⟩

def words05 : List Nat := [360585361975702672, 360585359003050640, 360585356030898100, 360585352778411501, 360585341418526462, 360585321747124002, 360585302079254210, 360585290546538006, 360585286797633596, 360585288988456755]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360502624185904680, 360502624859285650⟩, ⟨913651880665985530, 913656932439968506⟩, true⟩

def words06 : List Nat := [360585288988577854, 360585287018311598, 360585276947082125, 360585264138730304, 360585251332658339, 360585236396794289, 360585220448628097, 360585197376521789, 360585174308558707, 360585159360861077]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360412505088955534, 360412505763606579⟩, ⟨1912365956495274418, 1912371022335365712⟩, true⟩

def words07 : List Nat := [360585152566875474, 360585153227813830, 360585153227934067, 360585149791971859, 360585147069532405, 360585142140414122, 360585137212147094, 360585129445604795, 360585118004854836, 360585102426272226]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569168781311946, 360569169457239448⟩, ⟨175698875882640754, 175703955872302320⟩, true⟩

def words08 : List Nat := [360585086850473083, 360585071010797756, 360585059304297455, 360585055697307167, 360585052090956798, 360585041551536124, 360585027775375648, 360585022095657831, 360585016416921056, 360585012915839295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360519738786713589, 360519739463926685⟩, ⟨724365910572822987, 724371004826079449⟩, true⟩

def words09 : List Nat := [360585011487462870, 360585005972141470, 360585003028489522, 360585010343941302, 360585012011279937, 360585013678338382, 360585013678460074, 360585010943158784, 360585003992543428, 360584998113010116]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk110
