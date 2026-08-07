import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk039

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362380937565520009, 362380937740341446⟩, ⟨369824332561542485, 369824794952813101⟩, true⟩

def state01 : KState := ⟨⟨362313319337223540, 362313319512975537⟩, ⟨633743655834160683, 633744121859397249⟩, true⟩

def words00 : List Nat := [371275767394726027, 371275767394830312, 371275707489185482, 371275647328754706, 371275587199095702, 371275528209465322, 371275447864308847, 371275432794994559, 371275417733356685, 371275402408591752]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362702979858544550, 362702980035245788⟩, ⟨(-892061865308785488), (-892061395567228126)⟩, true⟩

def words01 : List Nat := [371275384637106345, 371275408296403040, 371275444064426917, 371275444064531780, 371275415979820667, 371275376367827612, 371275362178640848, 371275362178756084, 371275413352582454, 371275471390622675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362607485874362343, 362607486052010613⟩, ⟨(-517805816831856814), (-517805343372996332)⟩, true⟩

def words02 : List Nat := [371275529065570050, 371275529065675009, 371275572574527600, 371275626731569779, 371275698435446928, 371275710807244237, 371275710807325177, 371275695288900435, 371275728967063323, 371275762484630050]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362670740930407630, 362670741109004413⟩, ⟨(-765630280654644316), (-765629803463239014)⟩, true⟩

def words03 : List Nat := [371275860630081276, 371275958725664992, 371276050563176076, 371276090663247221, 371276149552657669, 371276208412204907, 371276316591561480, 371276369490766667, 371276418823744304, 371276468131723713]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362754676463609185, 362754676643153378⟩, ⟨(-1096119981712645201), (-1096119500783594323)⟩, true⟩

def words04 : List Nat := [371276542030316093, 371276586680998624, 371276695568113540, 371276804400069372, 371276902669850335, 371276915716848143, 371276992917279758, 371277070078667462, 371277178035250574, 371277248270391143]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362668020900252052, 362668021080763529⟩, ⟨(-752878310739056581), (-752877825984429079)⟩, true⟩

def words05 : List Nat := [371277318587500286, 371277388869069335, 371277503729411933, 371277586859719356, 371277674677063305, 371277762450059462, 371277849763575357, 371277852395034792, 371277900417502589, 371277948415783871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362571019169445943, 362571019350905328⟩, ⟨(-367684205076699930), (-367683716563411330)⟩, true⟩

def words06 : List Nat := [371278033719445838, 371278067933161591, 371278101860017505, 371278135769794600, 371278179126273585, 371278190845281977, 371278266012522917, 371278341141930764, 371278403805061506, 371278427128149496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362704218945194977, 362704219127616619⟩, ⟨(-897547591582467109), (-897547099244101993)⟩, true⟩

def words07 : List Nat := [371278472386772967, 371278517622665811, 371278605888823084, 371278610191992720, 371278610192075511, 371278604714708793, 371278633667245110, 371278648104745301, 371278704780954511, 371278761428735911]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362535376636596222, 362535376819982390⟩, ⟨(-225641301896264697), (-225640805714141827)⟩, true⟩

def words08 : List Nat := [371278817799991144, 371278819836582672, 371278845983319034, 371278872116987361, 371278916602794373, 371278916602901124, 371278877744261446, 371278839352076078, 371278825239479057, 371278839409380000]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362090449074440462, 362090449258792914⟩, ⟨1552859240842011561, 1552859740884564619⟩, true⟩

def words09 : List Nat := [371278893071368241, 371278946706521935, 371278988325876278, 371278988325983406, 371278946934126937, 371278909143335912, 371278871371401002, 371278857729407798, 371278761271895658, 371278664194014056]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk039
