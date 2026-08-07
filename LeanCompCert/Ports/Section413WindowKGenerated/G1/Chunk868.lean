import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk868

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481070024713355, 362481183713627381⟩, ⟨342231825008132990, 348894874412152166⟩, true⟩

def state01 : KState := ⟨⟨362480152435252871, 362480266151162712⟩, ⟨421905213999022262, 428570606780236844⟩, true⟩

def words00 : List Nat := [371285203195594534, 371285203190330560, 371285203196980937, 371285203257963143, 371285203297917338, 371285203300937507, 371285203163785727, 371285203083142238, 371285203028657788, 371285203031784533]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483593253115895, 362483706996527046⟩, ⟨123219839875340641, 129887620184814553⟩, true⟩

def words01 : List Nat := [371285202977177480, 371285202918842553, 371285202930222028, 371285202971270847, 371285203035568624, 371285203101064945, 371285203162635030, 371285203165655869, 371285203066491399, 371285203052967784]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468246652366808, 362468360422700833⟩, ⟨1455669466356161185, 1462339584249999233⟩, true⟩

def words02 : List Nat := [371285203065484334, 371285203068505089, 371285202921697126, 371285202750205402, 371285202577538781, 371285202418819792, 371285202206382992, 371285202083245627, 371285201959060382, 371285201832170487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490135728003237, 362490249525681535⟩, ⟨(-445065428657988989), (-438392936327928145)⟩, true⟩

def words03 : List Nat := [371285201640264507, 371285201562415737, 371285201517120661, 371285201520162429, 371285201437703709, 371285201322618532, 371285201220451320, 371285201223782456, 371285201238774932, 371285201300346407]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478757117339341, 362478870942321910⟩, ⟨543117828716594831, 549792692288936025⟩, true⟩

def words04 : List Nat := [371285201360872878, 371285201363947193, 371285201394839393, 371285201479067713, 371285201567387340, 371285201570409181, 371285201496239681, 371285201423270469, 371285201349064184, 371285201312987298]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473177216039576, 362473291068200729⟩, ⟨1027806885002512172, 1034484109169656938⟩, true⟩

def words05 : List Nat := [371285201301695021, 371285201364492052, 371285201416718473, 371285201419740461, 371285201295179322, 371285201194349985, 371285201119696168, 371285201122718388, 371285200989067562, 371285200855319883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484166488597649, 362484280367856013⟩, ⟨73235548219167856, 79915126184229902⟩, true⟩

def words06 : List Nat := [371285200720256075, 371285200718887655, 371285200659481858, 371285200656160180, 371285200651856472, 371285200626759902, 371285200477074071, 371285200376969957, 371285200303953835, 371285200307146726]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484115068053854, 362484228974860583⟩, ⟨77726622883969853, 84408594114012001⟩, true⟩

def words07 : List Nat := [371285200298819553, 371285200280817791, 371285200361683612, 371285200398925702, 371285200471540562, 371285200545283866, 371285200597358666, 371285200600402373, 371285200536051888, 371285200528660238]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472408374677387, 362472522308391778⟩, ⟨1094899669918129322, 1101583979028050612⟩, true⟩

def words08 : List Nat := [371285200632296707, 371285200635319770, 371285200573816988, 371285200513488789, 371285200451971037, 371285200432230404, 371285200345810937, 371285200313966753, 371285200281090275, 371285200222755089]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488979942188964, 362489093903242061⟩, ⟨(-345110926185557184), (-338424241476507802)⟩, true⟩

def words09 : List Nat := [371285200078935209, 371285199991450760, 371285199923705364, 371285199926733306, 371285199807229817, 371285199667449014, 371285199526400660, 371285199510538635, 371285199489702415, 371285199537912819]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk868
