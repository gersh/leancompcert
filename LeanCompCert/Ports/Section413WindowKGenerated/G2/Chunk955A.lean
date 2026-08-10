import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570135380014336, 360570195606244346⟩, ⟨1141170257084451233, 1145054029874538721⟩, true⟩

def state01 : KState := ⟨⟨360595652952178706, 360595713191489870⟩, ⟨(-1295916459171700117), (-1292031437066673223)⟩, true⟩

def words00 : List Nat := [360582185576387239, 360582185448328729, 360582185429251862, 360582185455474067, 360582185456750557, 360582185390445427, 360582185337006469, 360582185366127050, 360582185481575177, 360582185624643469]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575458800736204, 360575519053219984⟩, ⟨632913018668245489, 636799298956729901⟩, true⟩

def words01 : List Nat := [360582185691170302, 360582185757840135, 360582185798029894, 360582185893176001, 360582185913510297, 360582185934050035, 360582185935294910, 360582185901182183, 360582185780761853, 360582185712547421]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587824643411407, 360587884908957216⟩, ⟨(-548342420212296347), (-544454892174744041)⟩, true⟩

def words02 : List Nat := [360582185649181308, 360582185658553785, 360582185659790501, 360582185593227189, 360582185526424470, 360582185432423426, 360582185502434587, 360582185593072793, 360582185599534154, 360582185660627619]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609037711016125, 360609097989629583⟩, ⟨(-2574945644309570621), (-2571056867854644131)⟩, true⟩

def words03 : List Nat := [360582185831017679, 360582186001814373, 360582186257301785, 360582186450174286, 360582186536622884, 360582186623180976, 360582186741880277, 360582186915490953, 360582187198283528, 360582187481388570]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360616586082225301, 360616646374049428⟩, ⟨(-3296259023727889171), (-3292368985063959245)⟩, true⟩

def words04 : List Nat := [360582187709144725, 360582187938051887, 360582188163930089, 360582188390205294, 360582188571416169, 360582188778844723, 360582188930982535, 360582189083268568, 360582189344853989, 360582189707085567]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk955A
