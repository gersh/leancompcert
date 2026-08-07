import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588297465378691, 360588304278249510⟩, ⟨(-237883553034211325), (-237729237998143719)⟩, true⟩

def state01 : KState := ⟨⟨360591036842791427, 360591043659931242⟩, ⟨(-329755385228945510), (-329600927159701400)⟩, true⟩

def words00 : List Nat := [360581208095312664, 360581207741832549, 360581207972659852, 360581208532983249, 360581208867304553, 360581209076248874, 360581209076653136, 360581208647295898, 360581208217885012, 360581208055886013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360517666657864464, 360517673479223549⟩, ⟨2129347233664814961, 2129501833142691525⟩, true⟩

def words01 : List Nat := [360581208323410284, 360581208591003453, 360581208591402647, 360581208412576988, 360581207983938180, 360581207330039187, 360581206676036455, 360581206114003022, 360581204665046569, 360581202770188427]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569326078450035, 360569332904044579⟩, ⟨397433740968729043, 397588482439909815⟩, true⟩

def words02 : List Nat := [360581200875342203, 360581199868914884, 360581199461190183, 360581199027715857, 360581198594235170, 360581197373500700, 360581195266087434, 360581193414139103, 360581191562166990, 360581190598122716]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553202768339211, 360553209598200840⟩, ⟨938224881609811163, 938379766177208073⟩, true⟩

def words03 : List Nat := [360581190244888266, 360581189446141786, 360581188735767537, 360581189385471356, 360581189594443130, 360581189803474721, 360581189803881006, 360581189328502662, 360581188361698794, 360581187528021270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572863223349670, 360572870057430591⟩, ⟨278558570932474475, 278713597036359099⟩, true⟩

def words04 : List Nat := [360581186694243732, 360581186148796044, 360581185103698602, 360581183611885027, 360581182120079702, 360581180403546916, 360581179133760237, 360581178750890926, 360581178367995708, 360581177467178322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586768914138261, 360586775752458025⟩, ⟨(-188245616473399540), (-188090448135523884)⟩, true⟩

def words05 : List Nat := [360581177219941939, 360581176947123739, 360581176674188268, 360581176274040664, 360581175502643354, 360581173971814584, 360581172440991915, 360581171313143133, 360581171149844308, 360581171317306048]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581223952740859, 360581230795333594⟩, ⟨(-2419170650136560), (-2263858890209192)⟩, true⟩

def words06 : List Nat := [360581171317712542, 360581170818806539, 360581169739424976, 360581169546172947, 360581169352820502, 360581168510807210, 360581167418269102, 360581165769640736, 360581164121024870, 360581163360378121]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360516392376766539, 360516399223592686⟩, ⟨2174415213619407817, 2174570667515571087⟩, true⟩

def words07 : List Nat := [360581163930686182, 360581164501056718, 360581164519225291, 360581164519674083, 360581163654151905, 360581162210626293, 360581160767055494, 360581160208944549, 360581159063132196, 360581157135073198]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599974159040914, 360599981010100282⟩, ⟨(-632736915416952084), (-632581319347597294)⟩, true⟩

def words08 : List Nat := [360581155207026988, 360581154164357293, 360581153675772024, 360581152969503035, 360581152263241106, 360581150799817988, 360581149359839392, 360581148805029007, 360581148579765286, 360581149140869012]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593245995636621, 360593252850978862⟩, ⟨(-406769904269382904), (-406614164316854194)⟩, true⟩

def words09 : List Nat := [360581149256954497, 360581149373086266, 360581149463821243, 360581150227665791, 360581150766938086, 360581151306251725, 360581151401577927, 360581151402027033, 360581151238424548, 360581151599101929]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335
