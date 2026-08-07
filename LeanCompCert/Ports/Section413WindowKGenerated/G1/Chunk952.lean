import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484352801887237, 362484490539404943⟩, ⟨59774729698384041, 68627882081542415⟩, true⟩

def state01 : KState := ⟨⟨362482880501749294, 362483018269093134⟩, ⟨199987343987268086, 208843335972012478⟩, true⟩

def words00 : List Nat := [371285211473326317, 371285211488922235, 371285211613504155, 371285211739412399, 371285211827603899, 371285211830941117, 371285211782042566, 371285211752221493, 371285211767748984, 371285211771203963]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486370730461223, 362486508528213760⟩, ⟨(-132321293593834575), (-123462406244974739)⟩, true⟩

def words01 : List Nat := [371285211750683372, 371285211722570810, 371285211771813556, 371285211814044100, 371285211879981192, 371285211947264901, 371285212000029467, 371285212003367036, 371285211922451629, 371285211940210642]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473942590962292, 362474080418457235⟩, ⟨1051144599460634862, 1060006319036578610⟩, true⟩

def words02 : List Nat := [371285211987007607, 371285211990346366, 371285211910810275, 371285211832087755, 371285211752071901, 371285211695389925, 371285211586937350, 371285211535660808, 371285211483242572, 371285211430943181]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498843471012010, 362498981328719763⟩, ⟨(-1320294325085372631), (-1311429728197845889)⟩, true⟩

def words03 : List Nat := [371285211316321954, 371285211313872722, 371285211413522658, 371285211416869922, 371285211410535508, 371285211376458096, 371285211403370467, 371285211441342752, 371285211588186930, 371285211736546247]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481027859411381, 362481165747245853⟩, ⟨376554710007173944, 385422176319737784⟩, true⟩

def words04 : List Nat := [371285211879546894, 371285211931878533, 371285212030178541, 371285212130168272, 371285212256518803, 371285212259857426, 371285212239405540, 371285212213668422, 371285212186583684, 371285212174293830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472350868633179, 362472488786502742⟩, ⟨1203102997037273999, 1211973324340802845⟩, true⟩

def words05 : List Nat := [371285212136982600, 371285212143465458, 371285212148512437, 371285212151851485, 371285212021645043, 371285211926374928, 371285211840160408, 371285211843499296, 371285211709980379, 371285211580165778]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486610563646783, 362486748511433799⟩, ⟨(-155341416527778165), (-146468239136155821)⟩, true⟩

def words06 : List Nat := [371285211448872330, 371285211429327140, 371285211353492416, 371285211318184881, 371285211281799929, 371285211231684505, 371285211094623880, 371285211069592985, 371285211106434657, 371285211126089506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486866352438686, 362487004330655832⟩, ⟨(-179701816451640000), (-170825739826052586)⟩, true⟩

def words07 : List Nat := [371285211128602101, 371285211128646137, 371285211233996371, 371285211298039872, 371285211375478373, 371285211454160999, 371285211512125470, 371285211515465223, 371285211445070457, 371285211468072253]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487613994742663, 362487752002701825⟩, ⟨(-250918456852639833), (-242039546254942655)⟩, true⟩

def words08 : List Nat := [371285211587854244, 371285211626942461, 371285211664433769, 371285211703061747, 371285211735138393, 371285211738819558, 371285211801028382, 371285211889790743, 371285211968308236, 371285211998438517]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502065059212296, 362502203097362278⟩, ⟨(-1628061470599554380), (-1619179682964435470)⟩, true⟩

def words09 : List Nat := [371285212072924860, 371285212149104261, 371285212279495152, 371285212319394993, 371285212341783786, 371285212365261004, 371285212487019949, 371285212570137989, 371285212750687633, 371285212932694915]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk952
