import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk210

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362426529327832498, 362426535257198803⟩, ⟨1214869137604931564, 1214953346468547854⟩, true⟩

def state01 : KState := ⟨⟨362400025176555349, 362400031111743892⟩, ⟨1771677475514870221, 1771761806675865659⟩, true⟩

def words00 : List Nat := [371284387424038415, 371284386927704031, 371284383416923242, 371284379919952474, 371284376423071065, 371284373622942197, 371284369698430645, 371284366721254611, 371284363744130550, 371284360564703239]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362536018048627425, 362536023989715061⟩, ⟨(-1086184493694683087), (-1086100038563481749)⟩, true⟩

def words01 : List Nat := [371284356551561858, 371284354794190572, 371284353533683190, 371284353534350348, 371284352688608282, 371284351536261932, 371284351484992880, 371284351690213626, 371284354148902810, 371284356607641731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479906936678221, 362479912883683750⟩, ⟨93448855287821161, 93533434843061689⟩, true⟩

def words02 : List Nat := [371284358420751675, 371284358421407372, 371284359488460456, 371284361149063556, 371284363246808517, 371284363247463351, 371284362337116374, 371284361250991851, 371284360502283377, 371284360503029593]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466487238904218, 362466493191808616⟩, ⟨375943446602917390, 376028150241794536⟩, true⟩

def words03 : List Nat := [371284362332017857, 371284364372567067, 371284366167499782, 371284366168158017, 371284365806735901, 371284365507281856, 371284366962571211, 371284366963226659, 371284366100910335, 371284365252181325]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467219496339178, 362467225455117035⟩, ⟨360775376572702182, 360860203819304322⟩, true⟩

def words04 : List Nat := [371284365425780206, 371284365654227620, 371284367044345062, 371284368434587046, 371284369257504728, 371284369258162055, 371284367825968322, 371284367865276143, 371284368456994586, 371284368457673772]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488247986558988, 362488253951312346⟩, ⟨(-81923532636061467), (-81838579576217887)⟩, true⟩

def words05 : List Nat := [371284367643813039, 371284366812165752, 371284366836335102, 371284367065713782, 371284367990008368, 371284368914486989, 371284369852758916, 371284369853414732, 371284367978057627, 371284368163383178]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462756606595901, 362462762577193259⟩, ⟨455045197113756909, 455130273278854687⟩, true⟩

def words06 : List Nat := [371284370592772024, 371284370593427890, 371284370025471465, 371284368730173809, 371284367434746485, 371284366199334479, 371284363831929916, 371284363708393997, 371284363584658729, 371284363444458511]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508172164553924, 362508178141087242⟩, ⟨(-502077301390614927), (-501992100124986321)⟩, true⟩

def words07 : List Nat := [371284363074172865, 371284363729317687, 371284365892726221, 371284365893382720, 371284365485213091, 371284364757533146, 371284364240892967, 371284364241622280, 371284364473353675, 371284365603725401]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485566945536519, 362485572927992183⟩, ⟨(-25615785340899071), (-25530459201926293)⟩, true⟩

def words08 : List Nat := [371284366748506897, 371284366749163386, 371284365489838515, 371284365689600552, 371284366583592248, 371284366584251939, 371284365327980962, 371284363599210558, 371284362379152767, 371284362437299380]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362455115378497625, 362455121366869814⟩, ⟨616775178724554842, 616860629673377908⟩, true⟩

def words09 : List Nat := [371284363015977826, 371284363594853307, 371284364113669629, 371284364114326887, 371284362035536691, 371284360651090653, 371284359266425580, 371284359162868814, 371284357852685548, 371284356467802202]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk210
