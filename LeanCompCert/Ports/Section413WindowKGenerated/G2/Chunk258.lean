import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk258

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360549349807202363, 360549353758850688⟩, ⟨874864912591956787, 874933879158137915⟩, true⟩

def state01 : KState := ⟨⟨360615235106268987, 360615239061106027⟩, ⟨(-825224901895143129), (-825155853044593743)⟩, true⟩

def words00 : List Nat := [360583264795481389, 360583265657465784, 360583265657769876, 360583265546879967, 360583265435945077, 360583264978500663, 360583266594074837, 360583268209588285, 360583268667379517, 360583269906364073]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360667725208825423, 360667729166853254⟩, ⟨(-2180377737625490805), (-2180308606404393353)⟩, true⟩

def words01 : List Nat := [360583272150806823, 360583274395177965, 360583277726155368, 360583279563463636, 360583280134712351, 360583280705948975, 360583281495436019, 360583283269548627, 360583286540383841, 360583289811041923]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590521211035177, 360590525172291860⟩, ⟨(-187051152216900777), (-186981937611435097)⟩, true⟩

def words02 : List Nat := [360583292116528322, 360583292928925627, 360583292929205087, 360583292921229356, 360583292913165402, 360583292515818137, 360583291338972472, 360583289404654316, 360583287470419607, 360583286507988836]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360459825044713601, 360459829009155452⟩, ⟨3189693214673037307, 3189762511567664571⟩, true⟩

def words03 : List Nat := [360583287207590869, 360583287907202025, 360583287907503632, 360583287785665433, 360583286172217540, 360583284174640831, 360583282177124751, 360583280138087638, 360583276607842619, 360583271830810548]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580289994920878, 360580293962557236⟩, ⟨76217510402784450, 76286889859334266⟩, true⟩

def words04 : List Nat := [360583267054070355, 360583263771908804, 360583261433746694, 360583259999476379, 360583258565283321, 360583255869533808, 360583251683116909, 360583248990617782, 360583246298224861, 360583245099495702]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578991816264256, 360578995787127759⟩, ⟨109727537701397402, 109797000595784232⟩, true⟩

def words05 : List Nat := [360583244985643112, 360583243719446412, 360583242453282692, 360583242893100358, 360583243157044690, 360583243421023718, 360583243421330491, 360583242570804961, 360583241774622242, 360583241610816692]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567239061657571, 360567243035709558⟩, ⟨413486846534568397, 413556391899214811⟩, true⟩

def words06 : List Nat := [360583241501860694, 360583241502199468, 360583240604540493, 360583238724540800, 360583236844636138, 360583233931575613, 360583231764116460, 360583231088122184, 360583230412143054, 360583228980506590]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360632537609712153, 360632541586967666⟩, ⟨(-1276088934383183796), (-1276019306127785546)⟩, true⟩

def words07 : List Nat := [360583228598146592, 360583228833785883, 360583230559756401, 360583231812231015, 360583231812547125, 360583231671555871, 360583232505190922, 360583234452904364, 360583236358404918, 360583238263829929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604726244137485, 360604730224619414⟩, ⟨(-556699841736530302), (-556630129965042132)⟩, true⟩

def words08 : List Nat := [360583239414504887, 360583239414843893, 360583239078645065, 360583238235285802, 360583237391899194, 360583235883730282, 360583234709143261, 360583232780682657, 360583230852306395, 360583231243121402]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360530975950334154, 360530979934016694⟩, ⟨1353205049082596561, 1353274843733385321⟩, true⟩

def words09 : List Nat := [360583232560811026, 360583233878462855, 360583234022105348, 360583234090643097, 360583234090927118, 360583233776831633, 360583233462660672, 360583233019981866, 360583231945077839, 360583229927983234]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk258
