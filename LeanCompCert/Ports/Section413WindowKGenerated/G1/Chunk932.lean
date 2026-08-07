import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496808477070999, 362496940271194215⟩, ⟨(-1108209586829120244), (-1099916325418132590)⟩, true⟩

def state01 : KState := ⟨⟨362482245197354730, 362482377020862888⟩, ⟨249103996549337934, 257399996788185080⟩, true⟩

def words00 : List Nat := [371285138847337844, 371285138850598897, 371285138831218245, 371285138842576879, 371285138856963741, 371285138860227869, 371285138750183809, 371285138640932168, 371285138530325309, 371285138527104581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476738539646060, 362476870392532134⟩, ⟨762456712959179651, 770755451662992499⟩, true⟩

def words01 : List Nat := [371285138542564403, 371285138589003478, 371285138634949507, 371285138638240595, 371285138605646149, 371285138602585811, 371285138672251236, 371285138675513237, 371285138611594465, 371285138526534098]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487596773224075, 362487728655290436⟩, ⟨(-249790552954011048), (-241489093913157498)⟩, true⟩

def words02 : List Nat := [371285138454242858, 371285138457871826, 371285138428637388, 371285138444353085, 371285138446897528, 371285138432624186, 371285138321521213, 371285138311495547, 371285138400986113, 371285138432146706]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484268233382847, 362484400145292303⟩, ⟨60544456372432209, 68848697826009075⟩, true⟩

def words03 : List Nat := [371285138462979058, 371285138494930532, 371285138557396280, 371285138569593678, 371285138602559760, 371285138636784952, 371285138669563732, 371285138672826516, 371285138552049585, 371285138548314890]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473190507325450, 362473322448272981⟩, ⟨1093530097809590728, 1101837046924496664⟩, true⟩

def words04 : List Nat := [371285138649753396, 371285138653020991, 371285138638261676, 371285138624247636, 371285138609019206, 371285138606351348, 371285138545043018, 371285138496408433, 371285138446656321, 371285138395156890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk932
