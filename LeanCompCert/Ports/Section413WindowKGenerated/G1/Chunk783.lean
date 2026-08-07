import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480316198697698, 362480407980973336⟩, ⟨373621326816420756, 378474256217659070⟩, true⟩

def state01 : KState := ⟨⟨362485740624962474, 362485832431327489⟩, ⟨(-51081591879561154), (-46226776155086908)⟩, true⟩

def words00 : List Nat := [371285241665487543, 371285241678724145, 371285241684014176, 371285241690254033, 371285241745433875, 371285241748414021, 371285241878311502, 371285242026748810, 371285242123635749, 371285242133972647]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504652703579955, 362504744534420135⟩, ⟨(-1532168075894245295), (-1527311343397992365)⟩, true⟩

def words01 : List Nat := [371285242306329456, 371285242480122700, 371285242796379634, 371285242896243258, 371285242948299255, 371285243001218435, 371285243215966176, 371285243369572481, 371285243620404095, 371285243872485303]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479705729011943, 362479797584232268⟩, ⟨421763569489046645, 426622211564134801⟩, true⟩

def words02 : List Nat := [371285244123413550, 371285244157808503, 371285244235574871, 371285244314679676, 371285244421471841, 371285244424174796, 371285244313907197, 371285244201636711, 371285244088247823, 371285244056995758]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469029380980953, 362469121260520396⟩, ⟨1258126389751843523, 1262986936864438533⟩, true⟩

def words03 : List Nat := [371285244003867419, 371285244021333400, 371285244037845698, 371285244040549785, 371285243864806138, 371285243740516777, 371285243614786358, 371285243532452974, 371285243328722771, 371285243125938630]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487720164844378, 362487812068555800⟩, ⟨(-206157926778093552), (-201295485906298616)⟩, true⟩

def words04 : List Nat := [371285242921981488, 371285242882042732, 371285242832542627, 371285242884178457, 371285242910157417, 371285242912862335, 371285242748644235, 371285242748626008, 371285242882780570, 371285242918373846]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488349902613371, 362488441831025467⟩, ⟨(-255535837867984969), (-250671461575002341)⟩, true⟩

def words05 : List Nat := [371285242920441820, 371285242919672456, 371285242950570648, 371285242953581203, 371285242907789207, 371285242911880823, 371285242915053116, 371285242917806936, 371285242855450634, 371285242899649209]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481027241430543, 362481119193922914⟩, ⟨318300786545481251, 323167049892166681⟩, true⟩

def words06 : List Nat := [371285243057731522, 371285243060435832, 371285243001741747, 371285242943384472, 371285242884016744, 371285242832163951, 371285242735629192, 371285242770783991, 371285242797723504, 371285242800531211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493135210202862, 362493227187142706⟩, ⟨(-630627307071374558), (-625759127653086104)⟩, true⟩

def words07 : List Nat := [371285242846854593, 371285242947251202, 371285243197381193, 371285243246151472, 371285243256394595, 371285243267482816, 371285243384978877, 371285243422228965, 371285243525955419, 371285243630826085]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489413725897642, 362489505727278788⟩, ⟨(-338968850600001285), (-334098755350751517)⟩, true⟩

def words08 : List Nat := [371285243735881569, 371285243738586663, 371285243657222174, 371285243691153291, 371285243759313095, 371285243762084187, 371285243740121135, 371285243688744202, 371285243716808609, 371285243774307775]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479512992928349, 362479605018720016⟩, ⟨437264048367558001, 442136057277655521⟩, true⟩

def words09 : List Nat := [371285243984143112, 371285244195099654, 371285244373563777, 371285244384014948, 371285244443669537, 371285244504632452, 371285244648269304, 371285244650975058, 371285244578041490, 371285244509246517]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783
