import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360542001347156881, 360542013999636892⟩, ⟨1859613934300290282, 1859999546136888594⟩, true⟩

def state01 : KState := ⟨⟨360556158064560349, 360556170722875652⟩, ⟨1220920313448041183, 1221306188484792333⟩, true⟩

def words00 : List Nat := [360583254760797452, 360583253631314681, 360583252749582928, 360583251846660736, 360583250943731006, 360583249600167115, 360583248047662087, 360583246806315431, 360583245564824953, 360583244679614398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557267870866851, 360557280535056711⟩, ⟨1170788252604318427, 1171174392672190043⟩, true⟩

def words01 : List Nat := [360583244080005247, 360583243104199110, 360583242128318127, 360583241541373334, 360583241238979763, 360583240597763745, 360583239956514457, 360583239054308348, 360583237988920707, 360583237414326928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590549530226838, 360590562200243488⟩, ⟨(-330970530178976435), (-330584127177485109)⟩, true⟩

def words02 : List Nat := [360583236839553788, 360583236924978731, 360583236925531735, 360583236770681789, 360583236615739199, 360583236235507562, 360583236587932096, 360583237009700906, 360583237047218175, 360583237210166214]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360625860103388601, 360625872779234207⟩, ⟨(-1924808785930012603), (-1924422119838599715)⟩, true⟩

def words03 : List Nat := [360583237863313468, 360583238516612750, 360583239220388216, 360583239434624709, 360583239435201256, 360583239152466543, 360583239076508204, 360583239531460148, 360583240476426889, 360583241421492053]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565179185883175, 360565191867623573⟩, ⟨814465204670314131, 814852136880597651⟩, true⟩

def words04 : List Nat := [360583242053308453, 360583242195704083, 360583242325713059, 360583242455901649, 360583242461229235, 360583242461847162, 360583241977791202, 360583241190826994, 360583240403782538, 360583239533999666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451A
