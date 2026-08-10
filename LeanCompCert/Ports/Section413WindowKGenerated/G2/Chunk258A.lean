import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk258A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk258A
