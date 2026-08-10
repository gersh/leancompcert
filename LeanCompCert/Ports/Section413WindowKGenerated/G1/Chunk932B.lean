import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932A

def state06 : KState := ⟨⟨362500863535829946, 362500995506216116⟩, ⟨(-1487115016382034717), (-1478805321962495205)⟩, true⟩

def words05 : List Nat := [371285138270658138, 371285138262873588, 371285138356803317, 371285138367843202, 371285138370368009, 371285138363667806, 371285138460377780, 371285138528687080, 371285138700929456, 371285138874591295]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489657168504127, 362489789168374228⟩, ⟨(-441952443432642095), (-433639999192045395)⟩, true⟩

def words06 : List Nat := [371285139024804676, 371285139094899511, 371285139278941337, 371285139464721086, 371285139662070517, 371285139707136511, 371285139745748613, 371285139785470544, 371285139866921380, 371285139920492335]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475318454235337, 362475450483520155⟩, ⟨895539078326805132, 903854266223118780⟩, true⟩

def words07 : List Nat := [371285140056387611, 371285140193633945, 371285140329414294, 371285140332678366, 371285140325124088, 371285140306881460, 371285140353958389, 371285140357222422, 371285140273475611, 371285140173338156]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487060602663390, 362487192661177590⟩, ⟨(-199776300108661766), (-191458385546964242)⟩, true⟩

def words08 : List Nat := [371285140082776034, 371285140086436283, 371285140142186452, 371285140229952249, 371285140300694693, 371285140303959045, 371285140251150733, 371285140285082357, 371285140365095317, 371285140390481093]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485289746267987, 362485421834484227⟩, ⟨(-34559028176933356), (-26238342564529842)⟩, true⟩

def words09 : List Nat := [371285140392937599, 371285140394087317, 371285140476571501, 371285140514280941, 371285140577468023, 371285140642020764, 371285140697023719, 371285140700288441, 371285140604934499, 371285140611961805]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932B
