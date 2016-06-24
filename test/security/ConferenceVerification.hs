module ConferenceVerification where
import Prelude
       (Eq, Ord, Int, Bool, undefined, (<=), (==), (>=), (<), (>), (/=),
        (+), (-))
import {-# SOURCE #-} ConferenceImpl

data List a = Nil
            | Cons a (List a)
            deriving (Eq, Ord)

data Phase = Submission
           | Review
           | Done
           deriving (Eq, Ord)

data Status = NoDecision
            | Accepted
            | Rejected
            deriving (Eq, Ord)

test1 :: World -> PaperId -> World

test2 :: World -> PaperId -> World

test3 :: World -> PaperId -> World

test4 :: World -> PaperId -> World

test5 :: World -> PaperId -> World

test6 :: World -> PaperId -> World

selectFrom :: World -> Tagged User -> List PaperId -> Tagged String

test7 :: World -> List PaperId -> World
test1
  = (\ w ->
       (\ pid ->
          let title = ((getPaperTitle w) pid) in
            let authors = ((getPaperAuthors w) pid) in
              let st
                    = (((if_ (((lift2 eq) (getCurrentPhase w)) (return Done)))
                          ((getPaperStatus w) pid))
                         (return NoDecision))
                in
                let out = (((lift2 strcat) title) ((lift1 toString) st)) in
                  (((printAll w) authors) out)))
test2
  = (\ w ->
       (\ pid ->
          let ch = (getChair w) in
            let st = ((getPaperStatus w) pid) in
              (((print w) ch) ((lift1 toString) st))))
test3
  = (\ w ->
       (\ pid ->
          let u = (getSessionUser w) in
            let authors = ((getPaperAuthors w) pid) in
              let authors'
                    = (((if_ (((lift2 elem) u) authors)) authors) (return Nil))
                in let out = ((lift1 toString) authors') in (((print w) u) out)))
test4
  = (\ w ->
       (\ pid ->
          let u = (getSessionUser w) in
            let st
                  = (((if_ (((lift2 eq) (getChair w)) u)) ((getPaperStatus w) pid))
                       (((if_
                            (((lift2 and) (((lift2 eq) (getCurrentPhase w)) (return Done)))
                               (((lift2 elem) u) ((getPaperAuthors w) pid))))
                           ((getPaperStatus w) pid))
                          (return NoDecision)))
              in (((print w) u) ((lift1 toString) st))))
test5
  = (\ w ->
       (\ pid ->
          let u = (getSessionUser w) in
            let conflicts = ((getPaperConflicts w) pid) in
              let title
                    = (((if_ ((lift1 not) (((lift2 elem) u) conflicts)))
                          ((getPaperTitle w) pid))
                         (return emptyString))
                in
                let st
                      = (((if_
                             (((lift2 and) (((lift2 eq) (getCurrentPhase w)) (return Done)))
                                (((lift2 elem) u) ((getPaperAuthors w) pid))))
                            ((getPaperStatus w) pid))
                           (return NoDecision))
                  in
                  let ses
                        = ((bind st)
                             (\ s ->
                                if (s == Accepted) then ((getPaperSession w) pid) else
                                  (return emptyString)))
                    in
                    let out
                          = (((lift2 strcat) title)
                               (((lift2 strcat) ((lift1 toString) st)) ses))
                      in (((print w) u) out)))
test6
  = (\ w ->
       (\ pid ->
          let u = (getSessionUser w) in
            let conflicts = ((getPaperConflicts w) pid) in
              let noConflict = ((lift1 not) (((lift2 elem) u) conflicts)) in
                let title
                      = (((if_ noConflict) ((getPaperTitle w) pid)) (return emptyString))
                  in
                  let conflicts' = (((if_ noConflict) conflicts) (return Nil)) in
                    let out = (((lift2 strcat) title) ((lift1 toString) conflicts')) in
                      (((print w) u) out)))
selectFrom
  = (\ w ->
       (\ u ->
          (\ pids ->
             case pids of
                 Nil -> (return emptyString)
                 Cons pid rest -> let authors = ((getPaperAuthors w) pid) in
                                    let authors'
                                          = (((if_ (((lift2 elem) u) authors)) authors)
                                               (return Nil))
                                      in
                                      let line = ((lift1 toString) authors') in
                                        (((lift2 strcat) line) (((selectFrom w) u) rest)))))
test7
  = (\ w ->
       (\ allPids ->
          let u = (getSessionUser w) in
            (((print w) u) (((selectFrom w) u) allPids))))
