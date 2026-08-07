import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk220

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362434766497377536, 362434773030884339⟩, ⟨1083081784492947394, 1083178984993036348⟩, true⟩

def state01 : KState := ⟨⟨362456451513956390, 362456458053621352⟩, ⟨605999546450280841, 606096882461657889⟩, true⟩

def words00 : List Nat := [371284006201897130, 371284004820445855, 371284002659761188, 371284002562355681, 371284002464757517, 371284001992516361, 371283998770999984, 371283997190507312, 371283995609786006, 371283995394941737]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362433709614854682, 362433716160775953⟩, ⟨1106702608299228888, 1106800082043877536⟩, true⟩

def words01 : List Nat := [371283994144389340, 371283992256523686, 371283990540717405, 371283990541482089, 371283989682071290, 371283988424171095, 371283987166144288, 371283985719825489, 371283981843299114, 371283979561413732]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362443452892154225, 362443459444212660⟩, ⟨892279569919248196, 892377178836749224⟩, true⟩

def words02 : List Nat := [371283977279361339, 371283976283556964, 371283974505157334, 371283972735916655, 371283970966568892, 371283969799187744, 371283967605566954, 371283967470451681, 371283967335132453, 371283966805939249]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362529391595607401, 362529398153903012⟩, ⟨(-1001405136523152630), (-1001307390170679084)⟩, true⟩

def words03 : List Nat := [371283965186968413, 371283965407005126, 371283966666930378, 371283966667620128, 371283965739000023, 371283964712651547, 371283964715802475, 371283964721455468, 371283966783331620, 371283968845333951]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468322061057900, 362468328625588830⟩, ⟨344725962765293533, 344823846574876811⟩, true⟩

def words04 : List Nat := [371283970937307306, 371283970937996457, 371283970800636483, 371283970995764005, 371283971818083042, 371283971818772455, 371283970270053827, 371283968717142988, 371283967164082054, 371283966895274766]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362412099560212819, 362412106130933966⟩, ⟨1584974036587914067, 1585072056924420337⟩, true⟩

def words05 : List Nat := [371283967531827771, 371283968877718467, 371283970219237630, 371283970219927112, 371283968824244393, 371283967495450809, 371283966166425355, 371283965323019132, 371283962155232364, 371283958898700259]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478833963498318, 362478840540395125⟩, ⟨112570300913259005, 112668457516952373⟩, true⟩

def words06 : List Nat := [371283955642166946, 371283953748001768, 371283950830390775, 371283949965764868, 371283949100981663, 371283947897342046, 371283945402445161, 371283944960002156, 371283945589863137, 371283945590577135]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362519209961685619, 362519216544885815⟩, ⟨(-778766665760946820), (-778668370010489974)⟩, true⟩

def words07 : List Nat := [371283945359801090, 371283944742395163, 371283945557698978, 371283946246758652, 371283947539944127, 371283948833268799, 371283949620625185, 371283949621328976, 371283950766393632, 371283952364368154]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482965024933877, 362482971614280161⟩, ⟨21780859618959159, 21879291107327603⟩, true⟩

def words08 : List Nat := [371283955701365267, 371283956655986659, 371283957358457813, 371283958061089873, 371283958862850856, 371283958863618975, 371283959843173384, 371283961014012923, 371283962074910080, 371283962075624993]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362520330668011949, 362520337263605814⟩, ⟨(-803609723558133946), (-803511154029314778)⟩, true⟩

def words09 : List Nat := [371283964034426241, 371283966038244037, 371283970089331651, 371283971412227909, 371283972416441963, 371283973420783310, 371283975921185860, 371283977646347346, 371283979292059990, 371283980937917868]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk220
