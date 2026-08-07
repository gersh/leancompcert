import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360420561384135988, 360420563681726048⟩, ⟨3221147491126581661, 3221178434199578979⟩, true⟩

def state01 : KState := ⟨⟨360474268083728810, 360474270383729463⟩, ⟨2151929755004080802, 2151960746059683386⟩, true⟩

def words00 : List Nat := [360582423811286123, 360582415617184527, 360582408857078757, 360582402815098415, 360582396773705118, 360582388593508968, 360582379146296692, 360582370512074045, 360582361878637170, 360582354800909759]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360492596275596658, 360492598578023451⟩, ⟨1786863261829402095, 1786894301201820705⟩, true⟩

def words01 : List Nat := [360582349372759863, 360582342680539352, 360582335988941743, 360582331807559387, 360582328920456986, 360582324245963801, 360582319571912977, 360582313622632303, 360582306610324911, 360582302107200250]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360510201570767409, 360510203875602020⟩, ⟨1436014486124987630, 1436045573473118906⟩, true⟩

def words02 : List Nat := [360582297604444977, 360582293474236722, 360582289479799677, 360582283848039090, 360582278216801772, 360582271902527616, 360582267143788045, 360582264892159622, 360582262640734069, 360582258344918283]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578648270326836, 360578650577570551⟩, ⟨71306047848567298, 71337183222456394⟩, true⟩

def words03 : List Nat := [360582254729929522, 360582252190519326, 360582249651287806, 360582248576701780, 360582244989549695, 360582239254540205, 360582233520052934, 360582230289903222, 360582228348669974, 360582228169507485]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360502711985905162, 360502714295586447⟩, ⟨1585305395599160689, 1585336579589703603⟩, true⟩

def words04 : List Nat := [360582227990327149, 360582225805155410, 360582223425331815, 360582219356470787, 360582215287947898, 360582210579437708, 360582203361611987, 360582194669420150, 360582185978050982, 360582179788297711]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360435630112777457, 360435632424864651⟩, ⟨2924149869270508305, 2924181101271221373⟩, true⟩

def words05 : List Nat := [360582175805471530, 360582173534409444, 360582171263549033, 360582167714772508, 360582163851582880, 360582158555120066, 360582153259117050, 360582147905697661, 360582141823932255, 360582134484046576]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544975281702734, 360544977596203675⟩, ⟨741265829037548765, 741297109228622605⟩, true⟩

def words06 : List Nat := [360582127144838719, 360582122303882001, 360582118704867541, 360582117603457053, 360582116502133485, 360582112931825844, 360582107889365812, 360582104278060542, 360582100667041579, 360582098132469505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575877040515127, 360575879357456632⟩, ⟨123817551030206906, 123848879971382844⟩, true⟩

def words07 : List Nat := [360582096273981380, 360582092487583975, 360582088701516903, 360582087410361635, 360582087401912972, 360582085724073864, 360582084046373106, 360582081113415698, 360582078310061350, 360582078000097843]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360474135351193600, 360474137670543691⟩, ⟨2156989090917885315, 2157020467994955275⟩, true⟩

def words08 : List Nat := [360582077690079259, 360582076887143054, 360582074627073844, 360582071112953840, 360582067599147461, 360582062315909761, 360582058312032607, 360582053513318933, 360582048715058951, 360582042646431383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607149620393457, 360607151942165353⟩, ⟨(-502563668871387759), (-502532243370643307)⟩, true⟩

def words09 : List Nat := [360582037248960850, 360582034342824142, 360582031436897954, 360582031021778145, 360582029929312764, 360582026708793844, 360582023488548137, 360582024073127129, 360582025329731418, 360582026586264616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199
