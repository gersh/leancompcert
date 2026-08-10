import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360631576211439046, 360631597724089740⟩, ⟨(-2890251318225594603), (-2889405437625707593)⟩, true⟩

def state01 : KState := ⟨⟨360604749734082060, 360604771254378559⟩, ⟨(-1328957667516777271), (-1328111341892079677)⟩, true⟩

def words00 : List Nat := [360581953135922223, 360581953542015790, 360581953750672498, 360581953959403397, 360581953967927354, 360581954139680900, 360581954606441297, 360581955073343605, 360581955391281892, 360581955784074114]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360636896254651831, 360636917782634246⟩, ⟨(-3200349825123215475), (-3199503052064953039)⟩, true⟩

def words01 : List Nat := [360581956471881906, 360581957159935709, 360581957984158798, 360581958724005454, 360581959214266843, 360581959704576555, 360581960489871118, 360581961442951384, 360581962387562544, 360581963332314517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624930276494088, 360624951812221329⟩, ⟨(-2503823231259016073), (-2502976007258142397)⟩, true⟩

def words02 : List Nat := [360581964129642722, 360581964740696242, 360581965304917595, 360581965869353486, 360581966243789940, 360581966625341232, 360581966821056740, 360581967016850924, 360581967507537477, 360581968246641859]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615610916022850, 360615632459418982⟩, ⟨(-1961044030182694418), (-1960196359583868096)⟩, true⟩

def words03 : List Nat := [360581969280487155, 360581970314453431, 360581971097850016, 360581971838944734, 360581972438506283, 360581973038262573, 360581973932754102, 360581974662198779, 360581975240846083, 360581975819601949]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360635047015105781, 360635068566171117⟩, ⟨(-3093015865375726772), (-3092167748084232308)⟩, true⟩

def words04 : List Nat := [360581976628654442, 360581977648500527, 360581978963005596, 360581980277621346, 360581981296234213, 360581982020971693, 360581982668354043, 360581983315949482, 360581984140468421, 360581985052616256]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582A
