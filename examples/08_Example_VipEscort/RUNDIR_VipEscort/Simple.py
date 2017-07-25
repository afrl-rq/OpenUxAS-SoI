from enum import Enum

class Simple(object):
    
    __slots__ = ["_state", "_table"]
    
    def __init__(self):
        self._state = 4
    
    _table = [
        {   1: (1, 2),
        },
        {   2: (2, 4),
        },
        {   4: (3, 4),
        },
        {   4: (3, 4),
        },
        {   1: (0, 1),
        },
        ]
    
    def move(self, vlocs):
        try:
            table = self._table[self._state]
            newState,res = table[vlocs]
            self._state = newState
            return {
              "vloc": res,
            }
        
        except IndexError:
            raise Exception("Unrecognized internal state: " + str(self._state))
        
        except Exception:
            self._error(vlocs)
    
    def _error(self, vlocs):
        raise ValueError("Unrecognized input: " + (
            "vlocs = {vlocs}; ").format( vlocs=vlocs))