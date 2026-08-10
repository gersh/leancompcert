import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360610241917275374, 360610270570087439⟩, ⟨(-1828131854053778567), (-1826838952042693777)⟩, true⟩

def state01 : KState := ⟨⟨360588438938340229, 360588467600139890⟩, ⟨(-371759010258874690), (-370465507832369866)⟩, true⟩

def words00 : List Nat := [360582923327161656, 360582923396687649, 360582923500579867, 360582923604742544, 360582923612204358, 360582923613146913, 360582923397048974, 360582923036658681, 360582922676082353, 360582922622399214]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566439821370899, 360566468492043333⟩, ⟨1098187596271004716, 1099481691533472022⟩, true⟩

def words01 : List Nat := [360582922866099130, 360582923109972170, 360582923241909495, 360582923340279364, 360582923341083333, 360582923251310795, 360582923250311306, 360582923251254093, 360582923117614137, 360582922872341649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584288306034620, 360584316985618063⟩, ⟨(-94457320537118336), (-93162629798627256)⟩, true⟩

def words02 : List Nat := [360582922626858310, 360582922784729906, 360582923062782348, 360582923341005411, 360582923398760055, 360582923399702949, 360582923233848581, 360582923144748332, 360582923055387470, 360582922982389044]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578115933710707, 360578144622271723⟩, ⟨318039473107494846, 319334763861203536⟩, true⟩

def words03 : List Nat := [360582922983229168, 360582922893322539, 360582922803241940, 360582922724666780, 360582922725456033, 360582922698435314, 360582922671288727, 360582922532579049, 360582922292374074, 360582922221970425]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578025230490518, 360578053927947971⟩, ⟨324091834345198086, 325387719780526860⟩, true⟩

def words04 : List Nat := [360582922303087965, 360582922358003307, 360582922358866172, 360582922242542210, 360582922126066117, 360582921907502801, 360582921831409026, 360582921710924445, 360582921590340633, 360582921358311181]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668A
