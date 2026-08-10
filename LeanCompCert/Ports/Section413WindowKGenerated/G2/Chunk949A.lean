import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590225311480901, 360590284754323770⟩, ⟨(-777228139308483189), (-773418945184814637)⟩, true⟩

def state01 : KState := ⟨⟨360624991425812071, 360625050881626084⟩, ⟨(-4076712075445024753), (-4072901650295203035)⟩, true⟩

def words00 : List Nat := [360582135167165160, 360582135380534299, 360582135704494015, 360582136028710689, 360582136251776298, 360582136477564703, 360582136814052686, 360582137150947937, 360582137576543078, 360582138030109451]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597751117546019, 360597810586475177⟩, ⟨(-1491195587839871696), (-1487383917867069078)⟩, true⟩

def words01 : List Nat := [360582138405997537, 360582138782024716, 360582139104972090, 360582139484671402, 360582139812337944, 360582140140221963, 360582140400439411, 360582140550174200, 360582140716380227, 360582140883060053]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593789198967165, 360593848680847146⟩, ⟨(-1115137598307890848), (-1111324698978185684)⟩, true⟩

def words02 : List Nat := [360582141101648527, 360582141254116950, 360582141345024183, 360582141436070957, 360582141498882544, 360582141633157910, 360582141740122991, 360582141847333815, 360582141898638289, 360582142023390908]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617157169931533, 360617216664781638⟩, ⟨(-3333561722044699400), (-3329747591395317992)⟩, true⟩

def words03 : List Nat := [360582142223543855, 360582142424112361, 360582142735186838, 360582143049123957, 360582143269055618, 360582143489089872, 360582143800454780, 360582144167359472, 360582144537894437, 360582144908728981]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607641424622599, 360607700932605059⟩, ⟨(-2430211777654064079), (-2426396400155975191)⟩, true⟩

def words04 : List Nat := [360582145175159209, 360582145378198583, 360582145622113387, 360582145866427671, 360582146046151224, 360582146165431066, 360582146228823670, 360582146292389324, 360582146466562202, 360582146737281619]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949A
