###*
 * @author ZHANG Bei <zhang.bei@extjs.com>
 *         Sept 22, 2011
###
where = (obj, callback) ->
    res = {}
    for own key, item of obj
        res[key] = item if callback(key, item) != false
    res

key2arr = (obj) -> (key for own key, value of obj)
value2arr = (obj) -> (value for own key, value of obj)
value2pairs = (obj) -> ({key, value} for own key, value of obj)

Math.sgn = (x) ->
    if x > 0 then 1 else if x < 0 then -1 else 0
    
Math.nrand = () ->
    if Math.__lastc2?
        r = Math.__lastc2
        delete Math.__lastc2
        return r

    rad = 2
    while rad >= 1
        x1 = 2 * Math.random() - 1
        x2 = 2 * Math.random() - 1
        rad = x1 * x1 + x2 * x2

    return 0 if rad == 0
    c = Math.sqrt(-2 * Math.log(rad) / rad)
    Math.__lastc2 = x2 * c
    x1 * c

class DisjointSet
    ###*
     * @class DisjointSet
     * @constructor
    ###
    constructor: (list) ->
        @parent = {}
        @rank = {}
        for name in list
            @parent[name] = name
            @rank[name] = 0

    get: (name) ->
        return name if @parent[name] == name
        @parent[name] = @get(@parent[name])

    union: (x, y) ->
        x = @get(x)
        y = @get(y)
        return no if x == y
        rank = @rank
        parent = @parent
        if rank[x] > rank[y]
            parent[y] = parent[x]
        else
            parent[x] = parent[y]
            rank[y]++ if rank[x] == rank[y]
        yes


SpaceGrammar =
    Box : class
        constructor: (@name, @parts) ->
        draw: (ctx) ->
            me = this
            ctx.fillStyle = 'white'
            ctx.beginPath()
            ctx.rect(me.parts[0][0], me.parts[1][0], me.parts[0][1] - me.parts[0][0], me.parts[1][1] - me.parts[1][0])
            ctx.fill()
            ctx.stroke()
            ctx.fillStyle = 'black'
            ctx.fillText(me.name, (me.parts[0][0] + me.parts[0][1]) * 0.5 , (me.parts[1][0] + me.parts[1][1]) * 0.5)

    Parser : class
    
        constructor: () -> @reset()

        reset : () ->
        
        slotMap: # slots: [[0,0],[0,1],[0,2],[0,3],[0,4],[1,2],[1,3],[1,4],[2,2],[2,3],[2,4],[3,4],[4,4]]
            'R1' : [1, 3]
            'R2' : [1, 2]
            'R3' : [0, 2]
            'R4': [0, 3]
            'R5' : [2, 2]
            'R6' : [0, 4]
            'R7' : [0, 0]
            'R8' : [0, 1]

        parseWord: (word) ->
            return @slotMap[word] if @slotMap[word]
            return false if word.substr(0, 1) != '-'
            word = word.substr(1)
            slot = @slotMap[word] if @slotMap[word]
            return [4 - slot[1], 4 - slot[0]] if slot
            false

        parse: (text) ->
            regexp = /(\{.*?\})/g
            rules = []
            boxNames = {}
            text = text.replace('', '').replace(' ', '')
            while (matches = regexp.exec(text)) != null
                phrase = matches[1]
                phrase = phrase.substr(1, phrase.length - 2)
                words = phrase.split(',')
                a = words[0]
                b = words[1]
                x = @parseWord(words[2])
                y = @parseWord(words[3])
                z = @parseWord(words[4])
                rule = [a, b, x, y, z]
                rule.text = phrase
                rules.push(rule)
                boxNames[a] = []
                boxNames[b] = []
            [rules, key2arr boxNames]


    Generator : class

        constructor: () -> @reset()

        reset : () ->

        auxTag: ['x-', 'x+', 'y-', 'y+', 'z-', 'z+']

        config:
            farRange: [30, 60]
            nearRange: [5, 10]
            targetArea: [800, 2000]

        randomRange: (range) -> Math.abs(Math.nrand() * (range[1] - range[0]) * 0.5 + (range[1] + range[0]) * 0.5)

        # Analysis auxiliary lines and their relationships
        analysisAux: (rules, boxNames) ->
            aux = {box:{}}
            for dir, d in ['x', 'y', 'z']
                auxNames = []
                for name in boxNames
                    auxNames.push(name + dir + '+')
                    auxNames.push(name + dir + '-')
                ds = new DisjointSet(auxNames)
                parents = {}
                children = {}
                addRel = (lo, hi, type) ->
                    type ?= 'near'
                    if children[lo][hi]
                        if children[lo][hi] == 'near' and type == 'far'
                            children[lo][hi] = 'far'
                        return
                    parents[hi]++
                    children[hi].parents = parents[hi]
                    children[hi].top = false
                    children[lo][hi] = type

                # Merge equal axes
                for rule in rules
                    base = rule[0] + dir # name0
                    derived = rule[1] + dir # name1
                    continue if !base || !derived || base == derived || !(slot = rule[d + 2])
                    for sign, s in ['-', '+']
                        target = derived + sign
                        switch slot[s]
                            when 1 # target = base[0]
                                ds.union(target, base + '-')
                            when 3 # target = base[1]
                                ds.union(target, base + '+')

                # Default rules for each boxes
                for name in boxNames
                    if ds.get(name + dir + '-') == name + dir + '-'
                        parents[name + dir + '-'] = 0
                        children[name + dir + '-'] = { top : true, parents : 0 }
                    if ds.get(name + dir + '+') == name + dir + '+'
                        parents[name + dir + '+'] = 0
                        children[name + dir + '+'] = { top : true, parents : 0 }
                for name in boxNames
                    addRel ds.get(name + dir + '-'), ds.get(name + dir + '+'), 'far'

                
                # Construct axes DAG
                for rule in rules
                    base = rule[0] + dir # name0
                    derived = rule[1] + dir # name1
                    continue if !base || !derived  || !(slot = rule[d + 2])
                    basel = ds.get(base + '-')
                    baseh = ds.get(base + '+')
                    for sign, s in ['-', '+']
                        target = ds.get(derived + sign)
                        switch slot[s]
                            when 0 # target < basel
                                if ((slot[0] & 1) == 0 or (slot[1] & 1) == 0) and (target == basel)
                                    console.error('Contradictive rule: ' + rule.text)
                                else
                                    addRel target, basel
                            when 2
                                if ((slot[0] & 1) == 0 or (slot[1] & 1) == 0) and basel == target
                                    console.error('Contradictive rule: ' + rule.text)
                                else
                                    addRel basel, target
                                if ((slot[0] & 1) == 0 or (slot[1] & 1) == 0) and target == baseh
                                    console.error('Contradictive rule: ' + rule.text)
                                else
                                    addRel target, baseh
                            when 4
                                if ((slot[0] & 1) == 0 or (slot[1] & 1) == 0) and baseh == target
                                    console.error('Contradictive rule: ' + rule.text)
                                else
                                    addRel baseh, target

                # Check DAG for cycles
                queue = key2arr where parents, (key, item) -> item == 0
                bottom = 0
                while bottom < queue.length
                    curr = queue[bottom++]
                    for child of children[curr]
                        continue if child == 'top'
                        parents[child]--
                        if parents[child] == 0
                            queue.push(child)
                console.error("Contradictive rules. (Cyclic order on #{dir} axis)") if queue.length < parents.length
                for name in boxNames
                    aux['box'][name] ?= {}
                    aux['box'][name][dir] = [ds.get(name + dir + '-'), ds.get(name + dir + '+')]
                aux[dir] = where children, (key, item) -> (ds.get(key) == key)
            aux

        generateAux: (children) ->
            near = @config.nearRange
            far = @config.farRange
            results = {}
            for dir, d in ['x', 'y', 'z']
                position = {}
                aux = children[dir]
                parents = {}
                for name, a of aux
                    position[name] = []

                roots = key2arr where aux, (key, item) -> item.top
                for root, ri in roots
                    position[root] = [0, root]

                for name, a of aux
                    parents[name] = a.parents

                queue = roots.slice(0)
                bottom = 0

                while bottom < queue.length
                    curr = queue[bottom++]
                    pos = position[curr]
                    for child of aux[curr]
                        if child != 'top' and child != 'parents'
                            parents[child]--
                            next = pos[0] + switch aux[curr][child]
                                when 'near'
                                    @randomRange near
                                when 'far'
                                    @randomRange far

                            if position[child].length
                                if position[child][1] != pos[1]
                                    # Adjust cordinates to current root

                                    removingBranch = position[child][1]
                                    diff2 = next - position[child][0]
                                    
                                    for item in queue
                                        if position[item].length == 2 and position[item][1] == removingBranch
                                            position[item][0] += diff2
                                            position[item][1] = pos[1]
                                            
                                    position[child] = [next, pos[1]]
                                else
                                    position[child][0] = next if position[child][0] < next
                            else
                                position[child] = [next, pos[1]]
                            if parents[child] == 0
                                queue.push(child)

                results[dir] = {}
                results[dir][i] = position[i][0] for i in queue
            results

        beautifyAux: (auxinfo, results) ->
            delta = 5
            boxRange = @config.farRange
            targetArea = @config.targetArea
            for i in [1..100]
                presure =
                    x: {}
                    y: {}
                for name of auxinfo.x
                    presure.x[name] = 0
                for name of auxinfo.y
                    presure.y[name] = 0
                    
                for name, box of auxinfo.box
                    parts = (results[dir][axis] for axis in auxinfo.box[name][dir] for dir in ['x', 'y', 'z'])
                    sizex = parts[0][1] - parts[0][0]
                    sizey = parts[1][1] - parts[1][0]
                    ratio = sizex / sizey
                    ratio = Math.log(ratio)
                    ratio = Math.sgn(ratio) * Math.max(0, Math.abs(ratio) - Math.LN2)
                    continue if isNaN ratio
                    presure.x[auxinfo.box[name].x[0]] -= ratio
                    presure.x[auxinfo.box[name].x[1]] += ratio
                    presure.y[auxinfo.box[name].y[1]] -= ratio
                    presure.y[auxinfo.box[name].y[0]] += ratio
                    ratio = 0
                    if sizex < boxRange[0]
                        ratio = Math.log(boxRange[0] / sizex)
                    else if sizex > boxRange[1]
                        ratio = Math.log(boxRange[1] / sizex)
                    presure.x[auxinfo.box[name].x[0]] += ratio
                    presure.x[auxinfo.box[name].x[1]] -= ratio
                    ratio = 0
                    if sizey < boxRange[0]
                        ratio = Math.log(boxRange[0] / sizey)
                    else if sizey > boxRange[1]
                        ratio = Math.log(boxRange[1] / sizey)
                    presure.y[auxinfo.box[name].y[0]] += ratio
                    presure.y[auxinfo.box[name].y[1]] -= ratio

                    ratio = 0
                    area = sizex * sizey
                    if area < targetArea[0]
                        ratio = Math.log(targetArea[0] / area) / 2
                    else if area > targetArea[1]
                        ratio = Math.log(targetArea[1] / area) / 2
                    presure.x[auxinfo.box[name].x[0]] += ratio
                    presure.x[auxinfo.box[name].x[1]] -= ratio
                    presure.y[auxinfo.box[name].y[0]] += ratio
                    presure.y[auxinfo.box[name].y[1]] -= ratio

                for name of presure.x
                    results.x[name] -= presure.x[name] * delta
                for name of presure.y
                    results.y[name] -= presure.y[name] * delta
            return results


###
Initializting
###

if navigator.userAgent.match(/Android/i) or navigator.userAgent.match(/webOS/i) or
        navigator.userAgent.match(/iPhone/i) or navigator.userAgent.match(/iPad/i) or
        navigator.userAgent.match(/iPod/i)
    $.isTouch = true
    $('body').addClass('touch').bind 'touchstart', (ev) -> ev.preventDefault()
    $.clickEventName = 'touchstart'
else
    $.clickEventName = 'click'

sentences = []
parser = new SpaceGrammar.Parser
gen = new SpaceGrammar.Generator
rules = []
lastTemp = ''
boxNames = []
auxinfo = []
results =[]
boxes = []

ctx = $('canvas')[0].getContext('2d')
animtionInterval = 0
render = () ->
    ctx.clearRect 0, 0, $('canvas').width(), $('canvas').height()
    ctx.fillStyle = 'white'
    ctx.strokeStyle = 'black'
    ctx.lineWidth = 2
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    if sentences
        ctx.beginPath()
        rs = JSON.stringify(results)
        results = gen.beautifyAux auxinfo, results
        rs2 = JSON.stringify(results)
        boxes = []
        for name in boxNames
            parts = (results[dir][axis] for axis in auxinfo.box[name][dir] for dir in ['x', 'y', 'z'])
            boxes.push(new SpaceGrammar.Box(name, parts))
        minx = miny = -Infinity
        maxx = maxy = Infinity
        $.each(boxes, (k, b) ->
            minx = b.parts[0][0] if b.parts[0][0] > minx
            maxx = b.parts[0][1] if b.parts[0][1] < maxx
            miny = b.parts[1][0] if b.parts[1][0] > miny
            maxy = b.parts[1][1] if b.parts[1][1] < maxy
        )
        ctx.save()
        ctx.translate(($('canvas').width() - (minx + maxx)) * 0.5, ($('canvas').height() - (miny + maxy)) * 0.5)
        $.each(boxes, (k, b) -> b.draw(ctx))
        ctx.restore()

parse = () ->
    temp = parser.parse(localStorage.lastSentence = $('textarea').val())
    return if JSON.stringify(temp) == lastTemp
    lastTemp = JSON.stringify(temp)
    [rules ,boxNames] = temp
    auxinfo = gen.analysisAux rules ,boxNames
    results = gen.generateAux auxinfo
    temp

$('textarea').keydown((e) ->
    e.stopPropagation()
    if window.textareaDefer
        clearTimeout window.textareaDefer
        window.textareaDefer = false
    window.textareaDefer = setTimeout parse, 500
)

$('textarea').val(localStorage.lastSentence || '{A1,A2,R8,R4,R4}{A2,A3,R8,R6,R4}{A3,A4,R4,R8,R4}{A4,A5,-R8,R5,R4}{A5,A6,-R8,R5,R4}')
$('#dice').bind($.clickEventName, (e) ->
    e.stopPropagation()
    lastTemp = ''
    parse()
)
$('#open').bind($.clickEventName, (e) ->
    e.stopPropagation()
    $('.sentence').toggleClass('open');
    if $('.sentence').hasClass('open')
        $('#open').text('Collapse')
    else
        $('#open').text('Edit')
)
parse()
window.renderThread = setInterval render, 50

$(window).resize((e) ->
    $('canvas').attr('width', $('.result').width() - 2).attr('height', if $.isTouch then 605 else $('.result').height() - 2)
    render()
)
setTimeout((() -> $(window).resize()), $.isTouch ? 100 : 10)