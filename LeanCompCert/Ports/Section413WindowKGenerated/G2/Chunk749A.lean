import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590302667682310, 360590339019344990⟩, ⟨(-605358658062130913), (-603519653004140717)⟩, true⟩

def state01 : KState := ⟨⟨360600716888185959, 360600753249998709⟩, ⟨(-1385538443847672205), (-1383698678500291313)⟩, true⟩

def words00 : List Nat := [360582281473957233, 360582281475026242, 360582281574149068, 360582281713467120, 360582281778834793, 360582281863886962, 360582281864863884, 360582281784227159, 360582281767283195, 360582282015086610]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584599820066856, 360584636191914929⟩, ⟨(-178063523731825845), (-176223006586668647)⟩, true⟩

def words01 : List Nat := [360582282345305827, 360582282675719168, 360582282916821662, 360582283163441427, 360582283364925905, 360582283566698579, 360582283846844169, 360582284009410891, 360582284041764191, 360582284074263181]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599258176391195, 360599294558314210⟩, ⟨(-1276412694947108540), (-1274571422937788730)⟩, true⟩

def words02 : List Nat := [360582284075146740, 360582284030928312, 360582284231879820, 360582284433030172, 360582284467050051, 360582284468116547, 360582284324053545, 360582284289053398, 360582284395419777, 360582284623535043]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599378007239591, 360599414399319611⟩, ⟨(-1285383722767499109), (-1283541689643918271)⟩, true⟩

def words03 : List Nat := [360582284762376627, 360582284901343099, 360582285217964394, 360582285648989292, 360582285957853520, 360582286266873992, 360582286486672574, 360582286577418433, 360582286806834683, 360582287036599019]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609091868489830, 360609128270626198⟩, ⟨(-2013346548352444756), (-2011503761556299150)⟩, true⟩

def words04 : List Nat := [360582287443840084, 360582287904286194, 360582288229163172, 360582288554132342, 360582288781499339, 360582289098773372, 360582289556462608, 360582290014344345, 360582290327405071, 360582290686583874]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749A
