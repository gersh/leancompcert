import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk310

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452407271997486, 362452420624763488⟩, ⟨1022165175326793268, 1022444966615744328⟩, true⟩

def state01 : KState := ⟨⟨362458383041222192, 362458396402924260⟩, ⟨836934541032246327, 837214609383568731⟩, true⟩

def words00 : List Nat := [371285401657233725, 371285401373450975, 371285400566646168, 371285400025913354, 371285399484924266, 371285398832310617, 371285396991315701, 371285396019069790, 371285395046356403, 371285394616706381]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479648041895706, 362479661412660335⟩, ⟨177425932913798260, 177706282341681706⟩, true⟩

def words01 : List Nat := [371285393746850866, 371285392882934859, 371285392189946177, 371285392191054387, 371285391851563731, 371285391830122050, 371285391808350497, 371285391580741700, 371285390360858525, 371285390177403781]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362448911431429212, 362448924811069180⟩, ⟨1131072028792148579, 1131352653579382889⟩, true⟩

def words02 : List Nat := [371285390692829739, 371285390693827087, 371285390011537184, 371285389317058714, 371285388622215045, 371285388008271044, 371285386872037590, 371285386170921385, 371285385469523378, 371285384774123624]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483883296176391, 362483896684855477⟩, ⟨45608910520658151, 45889815836807835⟩, true⟩

def words03 : List Nat := [371285383599868188, 371285382473106794, 371285381345882996, 371285381253829990, 371285379930620134, 371285378433054557, 371285376935189888, 371285376221824902, 371285375140366705, 371285375093870839]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480047110378352, 362480060508067659⟩, ⟨164648094443798391, 164929279482588855⟩, true⟩

def words04 : List Nat := [371285375046996576, 371285374988230036, 371285374382278481, 371285374480768824, 371285374622914456, 371285374623915350, 371285373819344239, 371285372999317444, 371285372238943744, 371285372240096084]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362444691115288923, 362444704521968633⟩, ⟨1262816076927807102, 1263097541165325772⟩, true⟩

def words05 : List Nat := [371285372932287321, 371285373795902427, 371285374438868525, 371285374439867098, 371285373703067035, 371285373283883607, 371285373132818844, 371285373133817764, 371285372203047765, 371285370894832939]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362507702705682000, 362507716121299546⟩, ⟨(-694591974669856378), (-694310232776977014)⟩, true⟩

def words06 : List Nat := [371285369586268776, 371285369158956599, 371285368470379641, 371285368643233072, 371285368746373029, 371285368747389545, 371285368152895083, 371285368298634619, 371285369476141758, 371285370196392817]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497343287032269, 362497356711772569⟩, ⟨(-372689714160669348), (-372407688778408792)⟩, true⟩

def words07 : List Nat := [371285370921873699, 371285371647658245, 371285372642961427, 371285373118486128, 371285373657181705, 371285374196212784, 371285374740161235, 371285374741161067, 371285374481136655, 371285374867920106]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475838178872643, 362475851612511586⟩, ⟨295887840596277280, 296170142594760472⟩, true⟩

def words08 : List Nat := [371285376285767287, 371285376326664356, 371285376343395752, 371285376360452659, 371285376694470011, 371285376695588554, 371285377072158085, 371285377476842533, 371285377830280337, 371285377831314892]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362518209436272983, 362518222878933245⟩, ⟨(-1021617311838322279), (-1021334729320824135)⟩, true⟩

def words09 : List Nat := [371285378250271505, 371285378976085123, 371285380114159204, 371285380394588369, 371285380530223430, 371285380666168853, 371285381289460124, 371285381476151864, 371285382532824458, 371285383589864700]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk310
