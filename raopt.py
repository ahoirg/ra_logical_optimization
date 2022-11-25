import radb
import radb.ast
import radb.parse


def split_ra(tokens):
    stmr = []
    if hasattr(tokens, "attrs"):
        stmr.append(tokens.attrs)
        stmr.extend(split_ra(tokens.inputs[0]))
        return stmr

    if isinstance(tokens, radb.ast.Select):
        if isinstance(tokens.cond.inputs[0], radb.ast.ValExprBinaryOp):
            stmr.extend(split_ra(tokens.cond.inputs))
        else:
            stmr.append(tokens.cond)

        stmr.extend(split_ra(tokens.inputs[0]))
        return stmr

    if isinstance(tokens, radb.ast.ValExprBinaryOp):
        if isinstance(tokens.inputs[0], radb.ast.ValExprBinaryOp) \
                and isinstance(tokens.inputs[1], radb.ast.ValExprBinaryOp):
            stmr = [tokens.inputs[0], tokens.inputs[1]]
        else:
            stmr.append(tokens)

        return stmr

    if isinstance(tokens, radb.ast.Cross):
        stmr = ["Cross", split_ra(tokens.inputs[0]), split_ra(tokens.inputs[1])]
        return stmr

    if isinstance(tokens, radb.ast.RelRef):
        if tokens.inputs.__len__() == 0:
            stmr.append(tokens)

        return stmr

    if isinstance(tokens, radb.ast.Rename):
        stmr.append(tokens)

    if isinstance(tokens, list):
        for t in tokens:
            stmr.extend(split_ra(t))

    return stmr


def create_ra(stmt):
    if stmt[0] == "Cross":
        q = create_ra(stmt[1])
        q1 = create_ra(stmt[2])
        return radb.ast.Cross(q, q1)

    if stmt.__len__() > 2:
        stmt[1] = create_ra(stmt[1:])

    if isinstance(stmt[0], list) and isinstance(stmt[0][0], radb.ast.AttrRef):
        return radb.ast.Project(attrs=stmt[0], input=stmt[1])

    if isinstance(stmt[0], radb.ast.ValExprBinaryOp):
        if (not isinstance(stmt[1], radb.ast.RelRef)) and not (isinstance(stmt[1], radb.ast.Rename)):
            stmt[1] = radb.ast.RelRef("(" + str(stmt[1]) + ")")

        return radb.ast.Select(cond=stmt[0], input=stmt[1])

    if isinstance(stmt[0], radb.ast.RelRef) or isinstance(stmt[0], radb.ast.Rename):
        return stmt[0]


def get_selections(stmt, d):
    match_list = []
    if "Cross" in stmt:
        index = stmt.index("Cross")
        if index != -1:
            stmt1, l1, d = get_selections(stmt[index + 1], d)
            stmt2, l2, d = get_selections(stmt[index + 2], d)
            match_list.extend(l1)
            match_list.extend(l2)
            stmt = stmt[:index]
            stmt.extend(["Cross", stmt1, stmt2])

    for s in stmt:
        if isinstance(s, radb.ast.Rename):
            if s.inputs[0].rel in d.keys():
                d.__setitem__(s.relname, d[s.inputs[0].rel])

    for s in stmt:
        if isinstance(s, radb.ast.ValExprBinaryOp):
            if isinstance(s.inputs[0], radb.ast.AttrRef) and isinstance(s.inputs[1], radb.ast.AttrRef):
                match_list.extend(get_related_relations(s, d, True))
                continue

            match_list.extend(get_related_relations(s, d))

    for m in match_list:
        if m[0] in stmt:
            stmt.remove(m[0])

    return stmt, match_list, d


def get_related_relations(selection, d, double_atf=False):
    keys = d.keys()
    match_list = []

    if double_atf:
        match_list.append([selection, [selection.inputs[0].rel, selection.inputs[1].rel]])
        return match_list

    s_name = selection.inputs[0]
    if isinstance(selection.inputs[1], radb.ast.AttrRef):
        s_name = selection.inputs[1]

    if hasattr(s_name, "rel") and (s_name.rel is not None) and s_name.rel in keys:
        match_list.append([selection, s_name.rel])
    else:
        for k in keys:
            if s_name.name in d[k]:
                match_list.append([selection, k])

    return match_list


def __inner_rule_push_down_selections(stmt, match_list):
    if match_list.__len__() == 0:
        return stmt, []

    if "Cross" in stmt:
        index = stmt.index("Cross")
        if index != -1:
            stmt1, match_list = __inner_rule_push_down_selections(stmt[index + 1], match_list)
            stmt2, match_list = __inner_rule_push_down_selections(stmt[index + 2], match_list)
            stmt = stmt[:index]
            stmt.extend(["Cross", stmt1, stmt2])

    if match_list.__len__() == 0:
        return stmt, []

    r_index = -1
    for r in stmt:
        if isinstance(r, radb.ast.RelRef):
            if r.rel == match_list[1]:
                r_index = stmt.index(r)
                break
        if isinstance(r, radb.ast.Rename):
            if r.relname == match_list[1]:
                r_index = stmt.index(r)
                break

    if r_index != -1:
        stmt.insert(r_index, match_list[0])
        match_list = []

    return stmt, match_list


def get_alone_relation_in_cross(stmt, match_list):
    if not ("Cross" in stmt) or match_list == []:
        return stmt

    index = stmt.index("Cross")
    if index != 0:
        stmt1 = stmt[:index]
        stmt2, match_list = get_alone_relation_in_cross(stmt[index:], match_list)
        stmt1.extend(stmt2)
        return stmt1, match_list

    if "Cross" in stmt[1]:
        stmt[1], match_list = get_alone_relation_in_cross(stmt[1], match_list)

    if "Cross" in stmt[2]:
        stmt[2], match_list = get_alone_relation_in_cross(stmt[2], match_list)

    if match_list:
        search_list = [stmt[0]]
        search_list.extend(stmt[1])
        search_list.extend(stmt[2])
        temp = []
        for m in match_list[1]:
            for s in search_list:
                if isinstance(s, radb.ast.RelRef) and s.rel == m:
                    temp.append(m)
                elif isinstance(s, radb.ast.Rename) and s.relname == m:
                    temp.append(m)

        for t in temp:
            match_list[1].remove(t)

        if not match_list[1]:
            stmt.insert(0, match_list[0])
            match_list = []

    return stmt, match_list


def merge_selections(stmt):
    if "Cross" in stmt:
        index = stmt.index("Cross")
        if index != -1:
            stmt1 = merge_selections(stmt[index + 1])
            stmt2 = merge_selections(stmt[index + 2])
            stmt = stmt[:index]
            stmt.extend(["Cross", stmt1, stmt2])

    new_stmt = []
    for s in stmt:
        if not new_stmt:
            new_stmt.append(s)
            continue

        _len = len(new_stmt) - 1
        if isinstance(new_stmt[_len], radb.ast.ValExprBinaryOp) and isinstance(s, radb.ast.ValExprBinaryOp):
            new_stmt[_len] = radb.ast.ValExprBinaryOp(left=new_stmt[_len], op=11, right=s)
            continue

        new_stmt.append(s)

    return new_stmt


def reorder_cross_stmt(cross_stmt):
    stmr1 = cross_stmt[1]
    stmr2 = cross_stmt[2]
    if isinstance(stmr1, list) and "Cross" in stmr1:
        stmr1 = reorder_cross_stmt(stmr1)

    if isinstance(stmr1, list) and "Cross" in stmr2:
        stmr2 = reorder_cross_stmt(stmr2)

    temp = []
    for s in stmr1:
        if not isinstance(s, radb.ast.RelRef):
            temp.append(s)

    for t in temp:
        stmr1.remove(t)
        cross_stmt.insert(cross_stmt.index("Cross"), t)

    temp = []
    for s in stmr2:
        if not isinstance(s, radb.ast.RelRef):
            temp.append(s)

    for t in temp:
        stmr2.remove(t)
        cross_stmt.insert(cross_stmt.index("Cross"), t)

    i = cross_stmt.index("Cross")
    cross_stmt[i + 1], cross_stmt[i + 2] = stmr1, stmr2
    return cross_stmt


def __inner_rule_introduce_joins(stmt):
    if not ("Cross" in stmt):
        return stmt

    index = stmt.index("Cross")
    stmt1 = stmt[:index]
    stmt2 = stmt[index:]
    stmt2 = reorder_cross_stmt(stmt2)

    stmt1.extend(stmt2)
    stmt = stmt1

    return stmt


def __rule_introduce_joins(tokens):
    if isinstance(tokens, radb.ast.Select):
        if isinstance(tokens.cond, radb.ast.ValExprBinaryOp) and isinstance(tokens.inputs[0], radb.ast.Cross):
            left = __rule_introduce_joins(tokens.inputs[0].inputs[0])
            right = __rule_introduce_joins(tokens.inputs[0].inputs[1])
            return radb.ast.Join(left=left, right=right, cond=tokens.cond)

    elif isinstance(tokens, radb.ast.Project):
        if isinstance(tokens.inputs, list) and (not isinstance(tokens.inputs[0], radb.ast.RelRef)):
            return radb.ast.Project(tokens.attrs, __rule_introduce_joins(tokens.inputs[0]))

    return tokens


def rule_break_up_selections(tokens):
    stmt = split_ra(tokens)
    result = create_ra(stmt)
    return result


def rule_push_down_selections(tokens, d):
    tokens = radb.parse.one_statement_from_string(str(tokens) + ";")
    stmt = split_ra(tokens)
    stmt, match_list, d = get_selections(stmt, d)
    for m in match_list:
        if isinstance(m[1], list):
            stmt, _ = get_alone_relation_in_cross(stmt, m)
        else:
            stmt, _ = __inner_rule_push_down_selections(stmt, m)

    result = create_ra(stmt)
    return result


def rule_merge_selections(tokens):
    tokens = radb.parse.one_statement_from_string(str(tokens) + ";")
    stmt = merge_selections(split_ra(tokens))
    result = create_ra(stmt)
    return result


def rule_introduce_joins(tokens):
    tokens = radb.parse.one_statement_from_string(str(tokens) + ";")
    result = __rule_introduce_joins(tokens)
    return result
