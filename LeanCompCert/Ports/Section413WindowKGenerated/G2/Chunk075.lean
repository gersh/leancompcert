import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk075

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360447848124435407, 360447848421521825⟩, ⟨1010629888410909351, 1010631399320836859⟩, true⟩

def state01 : KState := ⟨⟨360498777759938269, 360498778057854571⟩, ⟨628140978005531318, 628142495143793884⟩, true⟩

def words00 : List Nat := [360582581310451100, 360582567978125534, 360582555938999718, 360582531600506125, 360582507268482941, 360582473408802236, 360582448819303257, 360582441802159133, 360582434786874461, 360582418869458272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360669161033845023, 360669161332595644⟩, ⟨(-653392177843652554), (-653390654435515546)⟩, true⟩

def words01 : List Nat := [360582407733755327, 360582387637916602, 360582367547402503, 360582349949792129, 360582334988939834, 360582304727969023, 360582274475032872, 360582262721655269, 360582274277393204, 360582285830077959]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579386001744346, 360579386301336558⟩, ⟨20829907411716737, 20831437152779325⟩, true⟩

def words02 : List Nat := [360582286161240161, 360582286161328542, 360582269357430255, 360582269705409358, 360582269705484776, 360582256452142675, 360582234644512811, 360582201515889176, 360582168396049097, 360582152760453793]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360218073257182878, 360218073557610046⟩, ⟨2743752502345989996, 2743754038378486884⟩, true⟩

def words03 : List Nat := [360582157416938729, 360582162439450769, 360582162439530496, 360582157738671278, 360582135605625929, 360582101060165620, 360582066523846654, 360582049438863811, 360582014934143286, 360581966666148307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360730708342432632, 360730708643696915⟩, ⟨(-1124307631615192124), (-1124306089266684290)⟩, true⟩

def words04 : List Nat := [360581918410934589, 360581887599918715, 360581866022325487, 360581851345781804, 360581836673121483, 360581807078598497, 360581786380968555, 360581783095666699, 360581793929794925, 360581813651077834]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360530340738829875, 360530341040941485⟩, ⟨389220157555715980, 389221706305715410⟩, true⟩

def words05 : List Nat := [360581824411326699, 360581835168735233, 360581837775555189, 360581849315703006, 360581856275855684, 360581863234180686, 360581863234260419, 360581856385751113, 360581832204524258, 360581825393627427]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360449676989297674, 360449677292247005⟩, ⟨999842580927297240, 999844136014748800⟩, true⟩

def words06 : List Nat := [360581829136446038, 360581832998728905, 360581832998808187, 360581828008917770, 360581823020332363, 360581806555643469, 360581802420766874, 360581790858617405, 360581779299513621, 360581757098853974]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360694898325412177, 360694898629201891⟩, ⟨(-857355075870591079), (-857353514417163759)⟩, true⟩

def words07 : List Nat := [360581739653435958, 360581732897076642, 360581736697989768, 360581748354105623, 360581748354187820, 360581744448979043, 360581753936280264, 360581776381455586, 360581791305308014, 360581806225242366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360676825177142108, 360676825481781912⟩, ⟨(-721467124554589369), (-721465556653306969)⟩, true⟩

def words08 : List Nat := [360581807230167937, 360581807230257288, 360581818339964658, 360581832529443378, 360581835752757653, 360581835752846842, 360581821785954458, 360581799009482849, 360581776238995445, 360581783253267447]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360440395753700479, 360440396059180576⟩, ⟨1074869130851656427, 1074870705134997917⟩, true⟩

def words09 : List Nat := [360581813024250711, 360581842787409605, 360581863750204750, 360581867550200515, 360581867550276655, 360581858561097280, 360581850922880777, 360581850922970162, 360581845026732989, 360581826415119392]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk075
