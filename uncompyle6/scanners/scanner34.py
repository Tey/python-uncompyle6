#  Copyright (c) 2015-2016 by Rocky Bernstein
"""
Python 3.4 bytecode scanner/deparser

This overlaps Python's 3.4's dis module, and in fact in some cases
we just fall back to that. But the intent is that it can be run from
Python 2 and other versions of Python. Also, we save token information
for later use in deparsing.
"""

from __future__ import print_function

import dis, inspect
from array import array
import uncompyle6.scanners.scanner3 as scan3

from uncompyle6.code import iscode
from uncompyle6.scanner import Token
from uncompyle6 import PYTHON3

# Get all the opcodes into globals
import uncompyle6.opcodes.opcode_34 as op3
globals().update(dis.opmap)

import uncompyle6.opcodes.opcode_34
# verify uses JUMP_OPs from here
JUMP_OPs = uncompyle6.opcodes.opcode_34.JUMP_OPs

from uncompyle6.opcodes.opcode_34 import *

class Scanner34(scan3.Scanner3):

    # Note: we can't use built-in disassembly routines, unless
    # we do post-processing like we do here.
    def disassemble(self, co, classname=None,
                    code_objects={}):
        # Container for tokens
        tokens = []
        customize = {}
        self.code = code = array('B', co.co_code)
        codelen = len(code)
        self.build_lines_data(co)
        self.build_prev_op()
        self.code_objects = code_objects

        # self.lines contains (block,addrLastInstr)
        if classname:
            classname = '_' + classname.lstrip('_') + '__'

            def unmangle(name):
                if name.startswith(classname) and name[-2:] != '__':
                    return name[len(classname) - 2:]
                return name

            free = [ unmangle(name) for name in (co.co_cellvars + co.co_freevars) ]
            names = [ unmangle(name) for name in co.co_names ]
            varnames = [ unmangle(name) for name in co.co_varnames ]
        else:
            free = co.co_cellvars + co.co_freevars
            names = co.co_names
            varnames = co.co_varnames
            pass

        # Scan for assertions. Later we will
        # turn 'LOAD_GLOBAL' to 'LOAD_ASSERT' for those
        # assertions

        self.load_asserts = set()
        for i in self.op_range(0, codelen):
            if self.code[i] == POP_JUMP_IF_TRUE and self.code[i+3] == LOAD_GLOBAL:
                if names[self.get_argument(i+3)] == 'AssertionError':
                    self.load_asserts.add(i+3)

        # Get jump targets
        # Format: {target offset: [jump offsets]}
        jump_targets = self.find_jump_targets()

        # contains (code, [addrRefToCode])
        last_stmt = self.next_stmt[0]
        i = self.next_stmt[last_stmt]
        replace = {}

        imports = self.all_instr(0, codelen, (IMPORT_NAME, IMPORT_FROM, IMPORT_STAR))
        if len(imports) > 1:
            last_import = imports[0]
            for i in imports[1:]:
                if self.lines[last_import].next > i:
                    if self.code[last_import] == IMPORT_NAME == self.code[i]:
                        replace[i] = 'IMPORT_NAME_CONT'
                last_import = i

        # Initialize extended arg at 0. When extended arg op is encountered,
        # variable preserved for next cycle and added as arg for next op
        extended_arg = 0

        for offset in self.op_range(0, codelen):
            # Add jump target tokens
            if offset in jump_targets:
                jump_idx = 0
                for jump_offset in jump_targets[offset]:
                    tokens.append(Token('COME_FROM', None, repr(jump_offset),
                                        offset='%s_%s' % (offset, jump_idx)))
                    jump_idx += 1
                    pass
                pass

            op = code[offset]
            op_name = op3.opname[op]

            oparg = None; pattr = None

            if op >= op3.HAVE_ARGUMENT:
                oparg = self.get_argument(offset) + extended_arg
                extended_arg = 0
                if op == op3.EXTENDED_ARG:
                    extended_arg = oparg * scan.L65536
                    continue
                if op in op3.hasconst:
                    const = co.co_consts[oparg]
                    if not PYTHON3 and isinstance(const, str):
                        if const in code_objects:
                            const = code_objects[const]
                    if iscode(const):
                        oparg = const
                        if const.co_name == '<lambda>':
                            assert op_name == 'LOAD_CONST'
                            op_name = 'LOAD_LAMBDA'
                        elif const.co_name == '<genexpr>':
                            op_name = 'LOAD_GENEXPR'
                        elif const.co_name == '<dictcomp>':
                            op_name = 'LOAD_DICTCOMP'
                        elif const.co_name == '<setcomp>':
                            op_name = 'LOAD_SETCOMP'
                        elif const.co_name == '<listcomp>':
                            op_name = 'LOAD_LISTCOMP'
                        # verify() uses 'pattr' for comparison, since 'attr'
                        # now holds Code(const) and thus can not be used
                        # for comparison (todo: think about changing this)
                        # pattr = 'code_object @ 0x%x %s->%s' %\
                        # (id(const), const.co_filename, const.co_name)
                        pattr = '<code_object ' + const.co_name + '>'
                    else:
                        pattr = const
                elif op in op3.hasname:
                    pattr = names[oparg]
                elif op in op3.hasjrel:
                    pattr = repr(offset + 3 + oparg)
                elif op in op3.hasjabs:
                    pattr = repr(oparg)
                elif op in op3.haslocal:
                    pattr = varnames[oparg]
                elif op in op3.hascompare:
                    pattr = op3.cmp_op[oparg]
                elif op in op3.hasfree:
                    pattr = free[oparg]

            if op_name in ['LOAD_CONST']:
                const = oparg
                if iscode(const):
                    if const.co_name == '<lambda>':
                        op_name = 'LOAD_LAMBDA'
                    elif const.co_name == '<genexpr>':
                        op_name = 'LOAD_GENEXPR'
                    elif const.co_name == '<dictcomp>':
                        op_name = 'LOAD_DICTCOMP'
                    elif const.co_name == '<setcomp>':
                        op_name = 'LOAD_SETCOMP'
                    elif const.co_name == '<listcomp>':
                        op_name = 'LOAD_LISTCOMP'
                    # verify() uses 'pattr' for comparison, since 'attr'
                    # now holds Code(const) and thus can not be used
                    # for comparison (todo: think about changing this)
                    # pattr = 'code_object @ 0x%x %s->%s' %\
                    # (id(const), const.co_filename, const.co_name)
                    pattr = '<code_object ' + const.co_name + '>'
                else:
                    pattr = const
                    pass
            elif op_name in ('BUILD_LIST', 'BUILD_TUPLE', 'BUILD_SET', 'BUILD_SLICE',
                            'UNPACK_SEQUENCE',
                            'MAKE_FUNCTION', 'MAKE_CLOSURE',
                            'DUP_TOPX', 'RAISE_VARARGS'
                            ):
                # if op_name == 'BUILD_TUPLE' and \
                #     self.code[self.prev[offset]] == LOAD_CLOSURE:
                #     continue
                # else:
                #     op_name = '%s_%d' % (op_name, oparg)
                #     if op_name != BUILD_SLICE:
                #         customize[op_name] = oparg
                op_name = '%s_%d' % (op_name, oparg)
                if op_name != 'BUILD_SLICE':
                    customize[op_name] = oparg

            elif op_name == 'JUMP_ABSOLUTE':
                pattr = oparg
                target = self.get_target(offset)
                if target < offset:
                    if (offset in self.stmts and
                        self.code[offset+3] not in (END_FINALLY, POP_BLOCK)
                        and offset not in self.not_continue):
                        op_name = 'CONTINUE'
                    else:
                        op_name = 'JUMP_BACK'

            elif offset in self.load_asserts:
                op_name = 'LOAD_ASSERT'

            if offset in self.linestarts:
                linestart = self.linestarts[offset]
            else:
                linestart = None

            tokens.append(
                Token(
                    type_ = op_name,
                    attr = oparg,
                    pattr = pattr,
                    offset = offset,
                    linestart = linestart,
                    )
                )
            pass
        return tokens, {}

    # FIXME: merge with scanner3 code
    def detect_structure(self, offset):
        """
        Detect structures and their boundaries to fix optimizied jumps
        in python2.3+
        """
        code = self.code
        op = code[offset]
        # Detect parent structure
        parent = self.structs[0]
        start = parent['start']
        end = parent['end']

        # Pick inner-most parent for our offset
        for struct in self.structs:
            curent_start = struct['start']
            curent_end   = struct['end']
            if (curent_start <= offset < curent_end) and (curent_start >= start and curent_end <= end):
                start = curent_start
                end = curent_end
                parent = struct
                pass

        if op in (POP_JUMP_IF_FALSE, POP_JUMP_IF_TRUE):
            start = offset + self.op_size(op)
            target = self.get_target(offset)
            rtarget = self.restrict_to_parent(target, parent)
            prev_op = self.prev_op

            # Do not let jump to go out of parent struct bounds
            if target != rtarget and parent['type'] == 'and/or':
                self.fixed_jumps[offset] = rtarget
                return

            # Does this jump to right after another cond jump?
            # If so, it's part of a larger conditional
            if (code[prev_op[target]] in (JUMP_IF_FALSE_OR_POP, JUMP_IF_TRUE_OR_POP,
                                          POP_JUMP_IF_FALSE, POP_JUMP_IF_TRUE)) and (target > offset):
                self.fixed_jumps[offset] = prev_op[target]
                self.structs.append({'type': 'and/or',
                                     'start': start,
                                     'end': prev_op[target]})
                return
            # Is it an and inside if block
            if op == POP_JUMP_IF_FALSE:
                # Search for other POP_JUMP_IF_FALSE targetting the same op,
                # in current statement, starting from current offset, and filter
                # everything inside inner 'or' jumps and midline ifs
                match = self.rem_or(start, self.next_stmt[offset], POP_JUMP_IF_FALSE, target)
                match = self.remove_mid_line_ifs(match)
                # If we still have any offsets in set, start working on it
                if match:
                    if (code[prev_op[rtarget]] in (JUMP_FORWARD, JUMP_ABSOLUTE) and prev_op[rtarget] not in self.stmts and
                        self.restrict_to_parent(self.get_target(prev_op[rtarget]), parent) == rtarget):
                        if (code[prev_op[prev_op[rtarget]]] == JUMP_ABSOLUTE and self.remove_mid_line_ifs([offset]) and
                            target == self.get_target(prev_op[prev_op[rtarget]]) and
                            (prev_op[prev_op[rtarget]] not in self.stmts or self.get_target(prev_op[prev_op[rtarget]]) > prev_op[prev_op[rtarget]]) and
                            1 == len(self.remove_mid_line_ifs(self.rem_or(start, prev_op[prev_op[rtarget]], (POP_JUMP_IF_FALSE, POP_JUMP_IF_TRUE), target)))):
                            pass
                        elif (code[prev_op[prev_op[rtarget]]] == RETURN_VALUE and self.remove_mid_line_ifs([offset]) and
                              1 == (len(set(self.remove_mid_line_ifs(self.rem_or(start, prev_op[prev_op[rtarget]],
                                                                                 (POP_JUMP_IF_FALSE, POP_JUMP_IF_TRUE), target))) |
                                    set(self.remove_mid_line_ifs(self.rem_or(start, prev_op[prev_op[rtarget]],
                                                                             (POP_JUMP_IF_FALSE, POP_JUMP_IF_TRUE, JUMP_ABSOLUTE),
                                                                             prev_op[rtarget], True)))))):
                            pass
                        else:
                            fix = None
                            jump_ifs = self.all_instr(start, self.next_stmt[offset], POP_JUMP_IF_FALSE)
                            last_jump_good = True
                            for j in jump_ifs:
                                if target == self.get_target(j):
                                    if self.lines[j].next == j + 3 and last_jump_good:
                                        fix = j
                                        break
                                else:
                                    last_jump_good = False
                            self.fixed_jumps[offset] = fix or match[-1]
                            return
                    else:
                        self.fixed_jumps[offset] = match[-1]
                        return
            # op == POP_JUMP_IF_TRUE
            else:
                next = self.next_stmt[offset]
                if prev_op[next] == offset:
                    pass
                elif code[next] in (JUMP_FORWARD, JUMP_ABSOLUTE) and target == self.get_target(next):
                    if code[prev_op[next]] == POP_JUMP_IF_FALSE:
                        if code[next] == JUMP_FORWARD or target != rtarget or code[prev_op[prev_op[rtarget]]] not in (JUMP_ABSOLUTE, RETURN_VALUE):
                            self.fixed_jumps[offset] = prev_op[next]
                            return
                elif (code[next] == JUMP_ABSOLUTE and code[target] in (JUMP_ABSOLUTE, JUMP_FORWARD) and
                      self.get_target(target) == self.get_target(next)):
                    self.fixed_jumps[offset] = prev_op[next]
                    return

            # Don't add a struct for a while test, it's already taken care of
            if offset in self.ignore_if:
                return

            if (code[prev_op[rtarget]] == JUMP_ABSOLUTE and prev_op[rtarget] in self.stmts and
                prev_op[rtarget] != offset and prev_op[prev_op[rtarget]] != offset and
                not (code[rtarget] == JUMP_ABSOLUTE and code[rtarget+3] == POP_BLOCK and code[prev_op[prev_op[rtarget]]] != JUMP_ABSOLUTE)):
                rtarget = prev_op[rtarget]

            # Does the if jump just beyond a jump op, then this is probably an if statement
            if code[prev_op[rtarget]] in (JUMP_ABSOLUTE, JUMP_FORWARD):
                if_end = self.get_target(prev_op[rtarget])

                # Is this a loop not an if?
                if (if_end < prev_op[rtarget]) and (code[prev_op[if_end]] == SETUP_LOOP):
                    if(if_end > start):
                        return

                end = self.restrict_to_parent(if_end, parent)

                self.structs.append({'type': 'if-then',
                                     'start': start,
                                     'end': prev_op[rtarget]})
                self.not_continue.add(prev_op[rtarget])

                if rtarget < end:
                    self.structs.append({'type': 'if-else',
                                         'start': rtarget,
                                         'end': end})
            elif code[prev_op[rtarget]] == RETURN_VALUE:
                self.structs.append({'type': 'if-then',
                                     'start': start,
                                     'end': rtarget})
                self.return_end_ifs.add(prev_op[rtarget])

        elif op in (JUMP_IF_FALSE_OR_POP, JUMP_IF_TRUE_OR_POP):
            target = self.get_target(offset)
            if target > offset:
                unop_target = self.last_instr(offset, target, JUMP_FORWARD, target)
                if unop_target and code[unop_target+3] != ROT_TWO:
                    self.fixed_jumps[offset] = unop_target
                else:
                    self.fixed_jumps[offset] = self.restrict_to_parent(target, parent)

    def next_except_jump(self, start):
        """
        Return the next jump that was generated by an except SomeException:
        construct in a try...except...else clause or None if not found.
        """

        if self.code[start] == DUP_TOP:
            except_match = self.first_instr(start, len(self.code), POP_JUMP_IF_FALSE)
            if except_match:
                jmp = self.prev_op[self.get_target(except_match)]
                self.ignore_if.add(except_match)
                self.not_continue.add(jmp)
                return jmp

        count_END_FINALLY = 0
        count_SETUP_ = 0
        for i in self.op_range(start, len(self.code)):
            op = self.code[i]
            if op == END_FINALLY:
                if count_END_FINALLY == count_SETUP_:
                    assert self.code[self.prev_op[i]] in (JUMP_ABSOLUTE, JUMP_FORWARD, RETURN_VALUE)
                    self.not_continue.add(self.prev_op[i])
                    return self.prev_op[i]
                count_END_FINALLY += 1
            elif op in (SETUP_EXCEPT, SETUP_WITH, SETUP_FINALLY):
                count_SETUP_ += 1

if __name__ == "__main__":
    co = inspect.currentframe().f_code
    tokens, customize = Scanner34(3.4).disassemble(co)
    for t in tokens:
        print(t)
    pass
