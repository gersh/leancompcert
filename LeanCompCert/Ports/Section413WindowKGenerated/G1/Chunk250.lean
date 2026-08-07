import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk250

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362455206330380352, 362455214859190299⟩, ⟨764739093477311514, 764883252714804804⟩, true⟩

def state01 : KState := ⟨⟨362464044381634204, 362464052917509946⟩, ⟨543807212304486656, 543951548222892208⟩, true⟩

def words00 : List Nat := [371285808966071511, 371285808882257060, 371285808018559419, 371285807963713223, 371285807908617302, 371285807614905636, 371285805191509788, 371285803760398464, 371285802328984153, 371285802279693989]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496443953315323, 362496452496389988⟩, ⟨(-266681808364816570), (-266537292364896066)⟩, true⟩

def words01 : List Nat := [371285801410708717, 371285800192634654, 371285799353014508, 371285799353889883, 371285799477899063, 371285799781943150, 371285800101832956, 371285800102636332, 371285799526094044, 371285799952831981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362458175004970036, 362458183555079506⟩, ⟨691068473266038375, 691213165312566909⟩, true⟩

def words02 : List Nat := [371285801795447566, 371285801796237436, 371285801512284232, 371285801191601235, 371285800870644801, 371285800356404451, 371285799129178467, 371285799080892887, 371285799032359005, 371285798943226233]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519296121529110, 362519304678801217⟩, ⟨(-839008493519877631), (-838863622156264437)⟩, true⟩

def words03 : List Nat := [371285798332235307, 371285798824883247, 371285800911812976, 371285800912603201, 371285800874853834, 371285800600605403, 371285801645364618, 371285802396029901, 371285803734526918, 371285805073268041]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362500468035711730, 362500476600109012⟩, ⟨(-367555400334634910), (-367410350519798594)⟩, true⟩

def words04 : List Nat := [371285806233407453, 371285806234199546, 371285806686833000, 371285807618527146, 371285809030826138, 371285809124088549, 371285809124690561, 371285808840329485, 371285809519345785, 371285810105736740]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482414720083224, 362482423291609868⟩, ⟨84759382720748520, 84904611161404078⟩, true⟩

def words05 : List Nat := [371285811314452748, 371285812523382522, 371285813429744759, 371285813430535522, 371285812215490314, 371285811481949336, 371285811605489235, 371285811606287621, 371285811479036435, 371285811344728839]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481427486591426, 362481436065189967⟩, ⟨109685107882375207, 109830513581508695⟩, true⟩

def words06 : List Nat := [371285812236283962, 371285812471836841, 371285814047961254, 371285815624291305, 371285816898722531, 371285816899513845, 371285816368211004, 371285816429899938, 371285817018242146, 371285817019062385]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483472150310068, 362483480736132553⟩, ⟨58498309279634872, 58643896118715408⟩, true⟩

def words07 : List Nat := [371285816844912946, 371285816556239747, 371285817567462192, 371285818308496645, 371285819040489625, 371285819772716704, 371285820495503753, 371285820496295411, 371285819101743928, 371285819009502518]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362457806016030109, 362457814608911157⟩, ⟨702264299821391395, 702410063725759573⟩, true⟩

def words08 : List Nat := [371285819476946103, 371285819477737839, 371285817922023881, 371285816340453202, 371285814758714351, 371285813449948745, 371285811454977638, 371285811048290969, 371285810641344186, 371285810227234225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495287368347658, 362495295968375881⟩, ⟨(-238393041608182879), (-238247098344871973)⟩, true⟩

def words09 : List Nat := [371285809112012648, 371285808802208463, 371285809317173077, 371285809317965267, 371285808029378370, 371285806309226241, 371285804588883403, 371285804455101846, 371285804051224168, 371285804430256091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk250
