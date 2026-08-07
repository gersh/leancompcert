import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk877

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582283439329585, 360582333894210247⟩, ⟨(-20814059698607894), (-17825925662892792)⟩, true⟩

def state01 : KState := ⟨⟨360595807646303560, 360595858113113465⟩, ⟨(-1206994700997612001), (-1204005520708356627)⟩, true⟩

def words00 : List Nat := [360582130769455637, 360582130978699531, 360582131074306669, 360582131170128671, 360582131171304246, 360582131155452296, 360582131009490535, 360582130969568066, 360582130993772276, 360582131151606832]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596508890982351, 360596559369815247⟩, ⟨(-1268511655133683578), (-1265521420249353330)⟩, true⟩

def words01 : List Nat := [360582131225994944, 360582131300513823, 360582131481283234, 360582131761540972, 360582131986868781, 360582132212397361, 360582132338178234, 360582132374106336, 360582132539593604, 360582132705501693]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598185718225022, 360598236208951007⟩, ⟨(-1415615383181344868), (-1412624104977064006)⟩, true⟩

def words02 : List Nat := [360582133000780869, 360582133236093023, 360582133392975410, 360582133550006073, 360582133606765975, 360582133729199610, 360582133926791826, 360582134124621223, 360582134257283558, 360582134442129963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600480697700380, 360600531200366442⟩, ⟨(-1617039180965648482), (-1614046855198380130)⟩, true⟩

def words03 : List Nat := [360582134600585508, 360582134759403748, 360582135005290027, 360582135121632825, 360582135127502516, 360582135133478943, 360582135134507684, 360582135195629759, 360582135406315785, 360582135617284435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592313539981704, 360592364054687350⟩, ⟨(-900481959256436964), (-897488577078577296)⟩, true⟩

def words04 : List Nat := [360582135763291400, 360582135853142715, 360582136072486258, 360582136292196058, 360582136402781108, 360582136420243698, 360582136421376872, 360582136339668337, 360582136263170145, 360582136381189857]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595676220351069, 360595726746965663⟩, ⟨(-1195518684638804806), (-1192524257390843254)⟩, true⟩

def words05 : List Nat := [360582136628478747, 360582136876026322, 360582137058401260, 360582137258777488, 360582137426354649, 360582137594263516, 360582137865824443, 360582138118179112, 360582138274174015, 360582138430317143]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606832167844085, 360606882706384999⟩, ⟨(-2174644093767109668), (-2171648619806266358)⟩, true⟩

def words06 : List Nat := [360582138591973760, 360582138819287866, 360582139042095790, 360582139265136352, 360582139377811956, 360582139493986021, 360582139739564010, 360582139985523169, 360582140211971591, 360582140495178493]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592212204189495, 360592262754787895⟩, ⟨(-891390308230193492), (-888393775926711086)⟩, true⟩

def words07 : List Nat := [360582140688408339, 360582140881768751, 360582141071696377, 360582141327230215, 360582141548668989, 360582141770313846, 360582141925643680, 360582141951457470, 360582142067776594, 360582142184551435]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360576988578745649, 360577039141232350⟩, ⟨445002743082370488, 448000319002752836⟩, true⟩

def words08 : List Nat := [360582142378599647, 360582142443252398, 360582142444379386, 360582142428375577, 360582142412165955, 360582142342174135, 360582142337392968, 360582142329658781, 360582142321788748, 360582142231778002]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598138060987374, 360598188635397882⟩, ⟨(-1411865470475329764), (-1408866847703623062)⟩, true⟩

def words09 : List Nat := [360582142174680529, 360582142085380651, 360582142034619827, 360582142078158406, 360582142079335226, 360582142011457240, 360582142003789764, 360582142130851567, 360582142314637612, 360582142498705776]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk877
