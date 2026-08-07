import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk285

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486512050330748, 362486523256846991⟩, ⟨(-42455437039158511), (-42239537800751183)⟩, true⟩

def state01 : KState := ⟨⟨362451500998392353, 362451512213007048⟩, ⟨955551482925936429, 955767613013141687⟩, true⟩

def words00 : List Nat := [371285041896579047, 371285041897488921, 371285040936210400, 371285039964008642, 371285038991502881, 371285038392080570, 371285037175668813, 371285036861688567, 371285036547437960, 371285036155939814]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500767820752675, 362500779043619545⟩, ⟨(-449330155719407804), (-449113790323476778)⟩, true⟩

def words01 : List Nat := [371285034980743927, 371285034319999713, 371285034224516168, 371285034225426662, 371285033368423860, 371285032314648517, 371285031433318628, 371285031434338889, 371285031714735961, 371285032267899077]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465794551691520, 362465805782773963⟩, ⟨548188557478373156, 548405157225281020⟩, true⟩

def words02 : List Nat := [371285032810277950, 371285032811192615, 371285032186330740, 371285032186034228, 371285032195311924, 371285032196224902, 371285030950501915, 371285029573665116, 371285028196544342, 371285027835252943]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362463043388138027, 362463054627421341⟩, ⟨626853716402333304, 627070550162345720⟩, true⟩

def words03 : List Nat := [371285027557664288, 371285027954150717, 371285028353287566, 371285028354204417, 371285027659644381, 371285027206263814, 371285027523702182, 371285027524615004, 371285027034346153, 371285026265478887]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362503696016840752, 362503707264283844⟩, ⟨(-533525988692972047), (-533308922011791907)⟩, true⟩

def words04 : List Nat := [371285025951975697, 371285025952979406, 371285026256952898, 371285026627723245, 371285026628433582, 371285026626715447, 371285025808354562, 371285026012523676, 371285027441202691, 371285028096408401]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503609007232266, 362503620263000475⟩, ⟨(-531042409708229957), (-530825105305142839)⟩, true⟩

def words05 : List Nat := [371285028757004768, 371285029417869270, 371285030590012169, 371285031148114032, 371285032077027995, 371285033006223277, 371285033869770595, 371285033870682228, 371285033948626813, 371285034600548000]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362452062223313635, 362452073487194057⟩, ⟨941470770626854430, 941688306757478814⟩, true⟩

def words06 : List Nat := [371285036066685453, 371285036067597062, 371285035902407395, 371285035740460725, 371285035666557746, 371285035667573612, 371285035236840656, 371285034917976992, 371285034598821275, 371285034225967508]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362534331196620162, 362534342468737766⟩, ⟨(-1409309593251804966), (-1409091821743057452)⟩, true⟩

def words07 : List Nat := [371285033142739686, 371285033213610812, 371285034507289095, 371285035103584754, 371285035495177688, 371285035887033848, 371285036815756370, 371285037319205959, 371285039044988319, 371285040771045486]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483549692590965, 362483560972948199⟩, ⟨42241354817352360, 42459361857311354⟩, true⟩

def words08 : List Nat := [371285042240451441, 371285042347122281, 371285043498826976, 371285044650940051, 371285046172436580, 371285046173349013, 371285046066087364, 371285045947139688, 371285046084250106, 371285046085290183]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482902302625501, 362482913591208618⟩, ⟨60915866348313030, 61134108607725984⟩, true⟩

def words09 : List Nat := [371285047203843033, 371285048374639021, 371285049521587350, 371285049644556660, 371285049788059605, 371285049931979366, 371285051296758884, 371285051297671915, 371285051221150163, 371285051147453644]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk285
