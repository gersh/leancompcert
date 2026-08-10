import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk558A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562055757204341, 360562075465419155⟩, ⟨1099625436041320581, 1100368447403238129⟩, true⟩

def state01 : KState := ⟨⟨360556645626398026, 360556665341922796⟩, ⟨1401475001189104199, 1402218420483298493⟩, true⟩

def words00 : List Nat := [360581794977299833, 360581794812765936, 360581794327923590, 360581793577256669, 360581792826476566, 360581791995252012, 360581791360728508, 360581791046688864, 360581790732586313, 360581790201634018]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603581638303636, 360603601361167268⟩, ⟨(-1218406133315627714), (-1217662304403242398)⟩, true⟩

def words01 : List Nat := [360581789752097382, 360581789127430529, 360581788502558356, 360581788198117982, 360581787984719818, 360581787487041850, 360581786989233003, 360581786882507024, 360581787273935438, 360581787665525785]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606098848709337, 360606118578967675⟩, ⟨(-1359049131923851750), (-1358304890202643058)⟩, true⟩

def words02 : List Nat := [360581787848375509, 360581788082613526, 360581788636872086, 360581789191338605, 360581789425667879, 360581789429759457, 360581789430457945, 360581789272836487, 360581789276806471, 360581789713459219]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563578318708656, 360563598056293403⟩, ⟨1015160104495280132, 1015904755286318702⟩, true⟩

def words03 : List Nat := [360581790343858489, 360581790974396993, 360581791397514580, 360581791500779879, 360581791501433201, 360581791425657910, 360581791593053645, 360581791593830672, 360581791518038322, 360581791193028474]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609841793503951, 360609861538423843⟩, ⟨(-1568421175778158005), (-1567676115356523329)⟩, true⟩

def words04 : List Nat := [360581790867855605, 360581790714489872, 360581791064776687, 360581791415200908, 360581791458600081, 360581791511171523, 360581791612527069, 360581791714106754, 360581792135373992, 360581792638755860]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk558A
