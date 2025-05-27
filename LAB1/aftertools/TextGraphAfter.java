import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.nio.charset.StandardCharsets;

/*
 * 从文本文件构建有向图，实现桥接词查询、新文本生成、最短路径计算、PageRank和随机游走
 */
public class TextGraphAfter{ //public类

    static class Graph {
        private Map<String, Node> nodes;    //有向图节点集合
        private boolean directed;           //是否为有向图标记      /***此标记？****/

        public Graph(boolean directed) {
            this.directed = directed;
            this.nodes = new HashMap<>();
        }

        public void addNode(String name) {
            nodes.putIfAbsent(name.toLowerCase(), new Node(name.toLowerCase()));
        }

        public void addEdge(String source, String destination, int weight) {
            String src = source.toLowerCase();
            String dest = destination.toLowerCase();

            addNode(src);   //先添加两个结点
            addNode(dest);

            Node srcNode = nodes.get(src);
            Node destNode = nodes.get(dest);

            srcNode.addEdge(destNode, weight);  //添加边和权重
            if (!directed) {    //如果非有向图则添加对称边
                destNode.addEdge(srcNode, weight);
            }
        }

        public Node getNode(String name) {
            return nodes.get(name.toLowerCase());
        }

        public boolean containsNode(String name) {
            return nodes.containsKey(name.toLowerCase());
        }

        public Collection<Node> getAllNodes() {
            return nodes.values();
        }

        public List<String> getBridgeWords(String word1, String word2) {
            word1 = word1.toLowerCase();
            word2 = word2.toLowerCase();

            if (!containsNode(word1) || !containsNode(word2)) {
                return null;
            }

            Node node1 = getNode(word1);
            Node node2 = getNode(word2);

            Set<String> neighbors = node1.getNeighbors();
            Set<String> predecessors = new HashSet<>();
            for (Node node : getAllNodes()) {
                if (node.hasEdgeTo(node2)) {
                    predecessors.add(node.getName());
                }
            }

            neighbors.retainAll(predecessors);
            return new ArrayList<>(neighbors);
        }

        public PathResult calcShortestPath(String source, String destination) {
            source = source.toLowerCase();
            destination = destination.toLowerCase();

            if (!containsNode(source) || !containsNode(destination)) {
                return null;
            }

            PriorityQueue<Node> queue = new PriorityQueue<>(Comparator.comparingInt(n -> n.getDistance()));
            Node start = getNode(source);
            start.setDistance(0);
            queue.add(start);

            Map<String, String> previous = new HashMap<>();
            Set<String> visited = new HashSet<>();

            while (!queue.isEmpty()) {
                Node current = queue.poll();
                visited.add(current.getName());

                for (Edge edge : current.getEdges()) {
                    Node neighbor = edge.getDestination();
                    if (visited.contains(neighbor.getName())) {
                        continue;
                    }

                    int newDist = current.getDistance() + edge.getWeight();
                    if (newDist < neighbor.getDistance()) {
                        neighbor.setDistance(newDist);
                        previous.put(neighbor.getName(), current.getName());
                        queue.add(neighbor);
                    }
                }
            }

            List<String> path = new ArrayList<>();
            String current = destination;
            while (current != null && !current.equals(source)) {
                path.add(current);
                current = previous.get(current);
                if (current == null) {
                    return new PathResult(null, Integer.MAX_VALUE); // 不可达
                }
            }
            path.add(source);
            Collections.reverse(path);

            int distance = getNode(destination).getDistance();

            for (Node node : getAllNodes()) {
                node.setDistance(Integer.MAX_VALUE);
            }

            return new PathResult(path, distance);
        }

        public Map<String, PathResult> calcShortestPathsFrom(String source) {
            source = source.toLowerCase();

            if (!containsNode(source)) {
                return null;
            }

            PriorityQueue<Node> queue = new PriorityQueue<>(Comparator.comparingInt(n -> n.getDistance()));
            Node start = getNode(source);
            start.setDistance(0);
            queue.add(start);

            Map<String, String> previous = new HashMap<>();
            Set<String> visited = new HashSet<>();

            while (!queue.isEmpty()) {
                Node current = queue.poll();
                visited.add(current.getName());

                for (Edge edge : current.getEdges()) {
                    Node neighbor = edge.getDestination();
                    if (visited.contains(neighbor.getName())) {
                        continue;
                    }

                    int newDist = current.getDistance() + edge.getWeight();
                    if (newDist < neighbor.getDistance()) {
                        neighbor.setDistance(newDist);
                        previous.put(neighbor.getName(), current.getName());
                        queue.add(neighbor);
                    }
                }
            }

            Map<String, PathResult> allPaths = new HashMap<>();
            for (String nodeName : nodes.keySet()) {
                if (nodeName.equals(source)) {
                    continue;
                }

                List<String> path = new ArrayList<>();
                String current = nodeName;
                while (current != null && !current.equals(source)) {
                    path.add(current);
                    current = previous.get(current);
                }

                if (current != null) { // 可达
                    path.add(source);
                    Collections.reverse(path);
                    allPaths.put(nodeName, new PathResult(path, getNode(nodeName).getDistance()));
                } else { // 不可达
                    allPaths.put(nodeName, new PathResult(null, Integer.MAX_VALUE));
                }
            }

            for (Node node : getAllNodes()) {
                node.setDistance(Integer.MAX_VALUE);
            }

            return allPaths;
        }

        public Map<String, Double> calcPageRank(double dampingFactor, int iterations) {
            Map<String, Double> pageRank = new HashMap<>();
            double initialValue = 1.0 / nodes.size();

            for (String node : nodes.keySet()) {
                pageRank.put(node, initialValue);
            }

            for (int i = 0; i < iterations; i++) {
                Map<String, Double> newPageRank = new HashMap<>();
                double danglingSum = 0.0;

                for (Node node : getAllNodes()) {
                    if (node.getEdges().isEmpty()) {
                        danglingSum += pageRank.get(node.getName());
                    }
                }

                for (Node node : getAllNodes()) {
                    double sum = 0.0;

                    for (Node incoming : getAllNodes()) {
                        if (incoming.hasEdgeTo(node)) {
                            sum += pageRank.get(incoming.getName()) / incoming.getOutDegree();
                        }
                    }

                    sum += danglingSum / nodes.size();

                    newPageRank.put(node.getName(),
                            (1 - dampingFactor) / nodes.size() + dampingFactor * sum);
                }

                pageRank = newPageRank;
            }

            return pageRank;
        }

        private static Map<String, Integer> calculateTermFrequencies(String text) {
            Map<String, Integer> frequencies = new HashMap<>();
            String[] words = text.replaceAll("[^a-zA-Z\\s]", " ")
                    .toLowerCase()
                    .split("\\s+");

            for (String word : words) {
                if (word.isEmpty()) {
                    continue;
                }
                frequencies.put(word, frequencies.getOrDefault(word, 0) + 1);
            }

            return frequencies;
        }

        private static Map<String, Double> calculateIdf(String text) {
            Map<String, Double> idf = new HashMap<>();
            String[] words = text.replaceAll("[^a-zA-Z\\s]", " ")
                    .toLowerCase()
                    .split("\\s+");

            int totalWords = words.length;
            Map<String, Integer> docFrequency = new HashMap<>();

            for (String word : words) {
                if (word.isEmpty()) {
                    continue;
                }
                docFrequency.put(word, docFrequency.getOrDefault(word, 0) + 1);
            }

            for (Map.Entry<String, Integer> entry : docFrequency.entrySet()) {
                idf.put(entry.getKey(), Math.log((double) totalWords / entry.getValue()));
            }

            return idf;
        }

        private static Map<String, Double> calculateTFIDF(String text) {
            Map<String, Integer> tf = calculateTermFrequencies(text);
            Map<String, Double> idf = calculateIdf(text);
            Map<String, Double> tfidf = new HashMap<>();

            //使用entrySet()遍历,代替keyset
            for (Map.Entry<String, Integer> entry : tf.entrySet()) {
                String word = entry.getKey();
                Integer frequency = entry.getValue();
                tfidf.put(word, frequency * idf.getOrDefault(word, 0.0));
            }

            double max = tfidf.values().stream().max(Double::compare).orElse(1.0);

            //使用entrySet()遍历,代替keyset
            for (Map.Entry<String, Double> entry : tfidf.entrySet()) {
                entry.setValue(entry.getValue() / max);
            }

            return tfidf;
        }

        public Map<String, Double> calcImprovedPageRank(Graph graph, double dampingFactor,
                                                        int iterations, String text) {
            Map<String, Double> tfidf = calculateTFIDF(text);
            Map<String, Double> pageRank = new HashMap<>();
            //double sumTfIdf = tfidf.values().stream().mapToDouble(Double::doubleValue).sum();

            for (String node : graph.nodes.keySet()) {
                double initialValue = tfidf.getOrDefault(node, 0.0);
                pageRank.put(node, initialValue + 0.0001);
            }

            double sum = pageRank.values().stream().mapToDouble(Double::doubleValue).sum();
            for (String node : pageRank.keySet()) {
                pageRank.put(node, pageRank.get(node) / sum);
            }

            for (int i = 0; i < iterations; i++) {
                Map<String, Double> newPageRank = new HashMap<>();
                double danglingSum = 0.0;

                for (Node node : graph.getAllNodes()) {
                    if (node.getEdges().isEmpty()) {
                        danglingSum += pageRank.get(node.getName());
                    }
                }

                for (Node node : graph.getAllNodes()) {
                    double sumPr = 0.0;

                    for (Node incoming : graph.getAllNodes()) {
                        if (incoming.hasEdgeTo(node)) {
                            sumPr += pageRank.get(incoming.getName()) / incoming.getOutDegree();
                        }
                    }

                    sumPr += danglingSum / graph.nodes.size();

                    double newValue = (1 - dampingFactor) * tfidf.getOrDefault(node.getName(), 1.0 / graph.nodes.size())
                            + dampingFactor * sumPr;
                    newPageRank.put(node.getName(), newValue);
                }

                double newSum = newPageRank.values().stream().mapToDouble(Double::doubleValue).sum();
                for (String node : newPageRank.keySet()) {
                    newPageRank.put(node, newPageRank.get(node) / newSum);
                }

                pageRank = newPageRank;
            }

            return pageRank;
        }

        public List<String> randomWalk() {
            List<String> walk = new ArrayList<>();
            if (nodes.isEmpty()) {
                return walk;
            }

            Random random = new Random();
            List<Node> nodeList = new ArrayList<>(getAllNodes());
            Node current = nodeList.get(random.nextInt(nodeList.size()));
            walk.add(current.getName());

            Set<String> visitedEdges = new HashSet<>();

            while (true) {
                List<Edge> edges = current.getEdges();
                if (edges.isEmpty()) break;

                Edge nextEdge = edges.get(random.nextInt(edges.size()));
                String edgeKey = current.getName() + "->" + nextEdge.getDestination().getName();

                if (visitedEdges.contains(edgeKey)) {
                    break; // 遇到重复边，停止
                }

                visitedEdges.add(edgeKey);
                current = nextEdge.getDestination();
                walk.add(current.getName());
            }

            return walk;
        }

        public String generateDot() {
            StringBuilder dot = new StringBuilder();
            dot.append("digraph G {\n");
            dot.append("  rankdir=LR;\n");
            dot.append("  node [shape=circle];\n");

            for (Node node : getAllNodes()) {
                dot.append("  \"").append(node.getName()).append("\";\n");
            }

            for (Node node : getAllNodes()) {
                for (Edge edge : node.getEdges()) {
                    dot.append("  \"")
                            .append(node.getName())
                            .append("\" -> \"")
                            .append(edge.getDestination().getName())
                            .append("\" [label=\"")
                            .append(edge.getWeight())
                            .append("\"];\n");
                }
            }

            dot.append("}\n");
            return dot.toString();
        }

        public void exportGraph(String format, String outputFile) {
            try {
                String dotContent = generateDot();
                Files.write(Paths.get("temp.dot"), dotContent.getBytes());

                ProcessBuilder pb = new ProcessBuilder(
                        "dot", "-T" + format, "temp.dot", "-o", outputFile);
                Process process = pb.start();
                int exitCode = process.waitFor();

                if (exitCode != 0) {
                    System.err.println("Graphviz执行失败，请确保已安装Graphviz");
                } else {
                    System.out.println("图形已保存为: " + outputFile);
                }

                Files.deleteIfExists(Paths.get("temp.dot"));
            } catch (IOException | InterruptedException e) {
                System.err.println("导出图形失败: " + e.getMessage());
            }
        }
    }

    static class Node {
        private String name;    //结点对应的字符串名称
        private List<Edge> edges;   //结点指出的边
        private int distance;   //用于最短路径计算

        public Node(String name) {
            this.name = name;
            this.edges = new ArrayList<>();
            this.distance = Integer.MAX_VALUE;
        }

        public String getName() {
            return name;
        }

        public void addEdge(Node destination, int weight) {
            for (Edge edge : edges) {
                if (edge.getDestination().equals(destination)) {
                    edge.setWeight(edge.getWeight() + weight); //如果存在则只是增加权重，不再添加新边
                    return;
                }
            }
            edges.add(new Edge(destination, weight));
        }

        public List<Edge> getEdges() {
            return edges;
        }

        public Set<String> getNeighbors() {
            return edges.stream()
                    .map(e -> e.getDestination().getName())
                    .collect(Collectors.toSet());
        }

        public boolean hasEdgeTo(Node node) {
            return edges.stream().anyMatch(e -> e.getDestination().equals(node));
        }

        public int getOutDegree() {
            return edges.size();
        }

        public int getDistance() {
            return distance;
        }

        public void setDistance(int distance) {
            this.distance = distance;
        }
    }

    static class Edge {
        private Node destination;   //有向边的终点
        private int weight;         //有向边对应的权重

        public Edge(Node destination, int weight) {
            this.destination = destination;
            this.weight = weight;
        }

        public Node getDestination() {
            return destination;
        }

        public int getWeight() {
            return weight;
        }

        public void setWeight(int weight) {
            this.weight = weight;
        }
    }

    static class PathResult {
        private List<String> path;
        private int distance;

        public PathResult(List<String> path, int distance) {
            this.path = path;
            this.distance = distance;
        }

        public List<String> getPath() {
            return path;
        }

        public int getDistance() {
            return distance;
        }
    }

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        Graph graph = null;

        while (true) {
            System.out.println("************************");
            System.out.println("文本图分析与处理程序");
            System.out.println("1. 从文件构建图");
            System.out.println("2. 显示图结构");
            System.out.println("3. 查询桥接词");
            System.out.println("4. 生成新文本");
            System.out.println("5. 计算最短路径");
            System.out.println("6. 计算PageRank");
            System.out.println("7. 随机游走");
            System.out.println("8. 导出图形");
            System.out.println("9. 计算改进的PageRank");
            System.out.println("0. 退出");
            System.out.println("************************");
            System.out.print("\n请选择功能(0-9): ");

            int choice;
            try {
                choice = scanner.nextInt();
                scanner.nextLine(); // 消耗换行符
            } catch (InputMismatchException e) {
                System.out.println("请输入有效数字!");
                scanner.nextLine(); // 清除无效输入
                continue;
            }

            switch (choice) {
                case 0:
                    System.out.println("程序退出。");
                    scanner.close();
                    return;

                case 1:
                    System.out.print("请输入文本文件路径: ");
                    String filePath = scanner.nextLine();
                    graph = buildGraphFromFile(filePath);
                    if (graph != null) {
                        System.out.println("图构建成功!");
                    } else {
                        System.out.println("图构建失败，请检查文件路径。");
                    }
                    break;

                case 2:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                    } else {
                        showDirectedGraph(graph);
                    }
                    break;

                case 3:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入第一个单词: ");
                    String word1 = scanner.nextLine();
                    System.out.print("请输入第二个单词: ");
                    String word2 = scanner.nextLine();
                    String result = queryBridgeWords(graph, word1, word2);
                    System.out.println(result);
                    break;

                case 4:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入新文本: ");
                    String inputText = scanner.nextLine();
                    String newText = generateNewText(graph, inputText);
                    System.out.println("生成的新文本: " + newText);
                    break;

                case 5:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入起始单词: ");
                    String startWord = scanner.nextLine();

                    System.out.print("请输入目标单词(留空将计算到所有其他节点的最短路径): ");
                    String endWord = scanner.nextLine();

                    if (endWord.isEmpty()) {
                        Map<String, PathResult> allPaths = graph.calcShortestPathsFrom(startWord);
                        if (allPaths == null) {
                            System.out.println("起始单词不存在!");
                            break;
                        }

                        System.out.println("从 '" + startWord + "' 到其他所有单词的最短路径:");
                        allPaths.entrySet().stream()
                                .sorted(Comparator.comparingInt(e -> e.getValue().getDistance()))
                                .forEach(entry -> {
                                    PathResult pathResult = entry.getValue();
                                    System.out.printf("到 %s: ", entry.getKey());
                                    if (pathResult.getPath() == null) {
                                        System.out.println("不可达");
                                    } else {
                                        System.out.printf("路径: %s, 距离: %d%n",
                                                String.join(" -> ", pathResult.getPath()),
                                                pathResult.getDistance());
                                    }
                                });
                    } else {
                        PathResult pathResult = graph.calcShortestPath(startWord, endWord);
                        if (pathResult == null || pathResult.getPath() == null) {
                            System.out.println("单词不存在或路径不可达!");
                        } else {
                            System.out.println("最短路径: " + String.join(" -> ", pathResult.getPath()));
                            System.out.println("路径长度: " + pathResult.getDistance());
                        }
                    }
                    break;

                case 6:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入要查询的单词(留空显示全部): ");
                    String word = scanner.nextLine();
                    Map<String, Double> pageRanks = graph.calcPageRank(0.85, 50);
                    if (word.isEmpty()) {
                        System.out.println("所有单词的PageRank值:");
                        pageRanks.entrySet().stream()
                                .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                                .forEach(e -> System.out.printf("%s: %.4f%n", e.getKey(), e.getValue()));
                    } else {
                        word = word.toLowerCase();
                        if (pageRanks.containsKey(word)) {
                            System.out.printf("%s的PageRank值: %.4f%n", word, pageRanks.get(word));
                        } else {
                            System.out.println("单词不存在于图中!");
                        }
                    }
                    break;

                case 7:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    List<String> walk = graph.randomWalk();
                    System.out.println("随机游走结果: " + String.join(" -> ", walk));
                    System.out.print("是否保存到文件?(y/n): ");
                    String save = scanner.nextLine();
                    if (save.equalsIgnoreCase("y")) {
                        System.out.print("请输入文件名: ");
                        String fileName = scanner.nextLine();
                        saveRandomWalk(walk, fileName);
                    }
                    break;
                case 8:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入输出文件名(不含扩展名): ");
                    final String outputFile = scanner.nextLine();
                    System.out.print("请选择格式(1-png, 2-svg, 3-pdf): ");
                    int formatChoice = scanner.nextInt();
                    scanner.nextLine(); // 消耗换行符

                    String format;
                    switch (formatChoice) {
                        case 1:
                            format = "png";
                            break;
                        case 2:
                            format = "svg";
                            break;
                        case 3:
                            format = "pdf";
                            break;
                        default:
                            System.out.println("无效选择，默认使用png");
                            format = "png";
                    }
                    graph.exportGraph(format, outputFile + "." + format);
                    break;

                case 9:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入原始文本文件路径(用于TF-IDF计算): ");
                    String textFilePath = scanner.nextLine();
                    try {
                        String textContent = new String(Files.readAllBytes(Paths.get(textFilePath)),StandardCharsets.UTF_8);
                        System.out.print("请输入要查询的单词(留空显示全部): ");
                        String wordForimprovePr = scanner.nextLine();

                        Map<String, Double> improvePr = graph.calcImprovedPageRank(graph, 0.85, 50, textContent);

                        if (wordForimprovePr.isEmpty()) {
                            System.out.println("所有单词的改进PageRank值(TF-IDF加权):");
                            improvePr.entrySet().stream()
                                    .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                                    .forEach(e -> System.out.printf("%s: %.4f%n", e.getKey(),
                                            e.getValue()));
                        } else {
                            wordForimprovePr = wordForimprovePr.toLowerCase();
                            if (improvePr.containsKey(wordForimprovePr)) {
                                System.out.printf("%s的改进PageRank值: %.4f%n",
                                        wordForimprovePr, improvePr.get(wordForimprovePr));
                            } else {
                                System.out.println("单词不存在于图中!");
                            }
                        }
                    } catch (IOException e) {
                        System.out.println("读取文件错误: " + e.getMessage());
                    }
                    break;

                default:
                    System.out.println("无效选择，请重新输入!");
            }
        }
    }

    public static Graph buildGraphFromFile(String filePath) {
        try {
            String content = new String(Files.readAllBytes(Paths.get(filePath)),StandardCharsets.UTF_8);
            return buildGraph(content);
        } catch (IOException e) {
            System.err.println("读取文件错误: " + e.getMessage());
            return null;
        }
    }

    public static Graph buildGraph(String text) {
        String processed = text.replaceAll("[^a-zA-Z\\s]", " ")
                .replaceAll("\\s+", " ")
                .toLowerCase();

        String[] words = processed.split("\\s+");
        if (words.length == 0) {
            return null;
        }

        Graph graph = new Graph(true);

        for (int i = 0; i < words.length - 1; i++) {
            String current = words[i];
            String next = words[i + 1];
            graph.addEdge(current, next, 1);
        }

        return graph;
    }

    public static void showDirectedGraph(Graph graph) {
        System.out.println("有向图结构:");
        for (Node node : graph.getAllNodes()) {
            System.out.print(node.getName() + " -> ");
            List<Edge> edges = node.getEdges();
            if (edges.isEmpty()) {
                System.out.println("无出边");
                continue;
            }

            List<String> edgeStrings = edges.stream()
                    .map(e -> e.getDestination().getName() + "(" + e.getWeight() + ")") //括号中显示边的权重值
                    .collect(Collectors.toList());
            System.out.println(String.join(", ", edgeStrings));
        }
    }

    public static String queryBridgeWords(Graph graph, String word1, String word2) {
        word1 = word1.toLowerCase();
        word2 = word2.toLowerCase();

        if (!graph.containsNode(word1) || !graph.containsNode(word2)) {
            return "No " + (!graph.containsNode(word1) ? word1 : word2) + " in the graph!";
        }

        List<String> bridgeWords = graph.getBridgeWords(word1, word2);
        if (bridgeWords == null || bridgeWords.isEmpty()) {
            return "No bridge words from " + word1 + " to " + word2 + "!";
        }

        if (bridgeWords.size() == 1) {
            return "The bridge word from " + word1 + " to " + word2 + " is: " + bridgeWords.get(0);
        } else {
            String last = bridgeWords.remove(bridgeWords.size() - 1);
            return "The bridge words from " + word1 + " to " + word2 + " are: "
                    + String.join(", ", bridgeWords) + " and " + last;
        }
    }

    public static String generateNewText(Graph graph, String inputText) {
        String processed = inputText.replaceAll("[^a-zA-Z\\s]", " ")
                .replaceAll("\\s+", " ")
                .toLowerCase();

        String[] words = processed.split("\\s+");
        if (words.length == 0) {
            return inputText;
        }

        List<String> result = new ArrayList<>();
        result.add(words[0]);

        Random random = new Random();

        for (int i = 0; i < words.length - 1; i++) {
            String current = words[i];
            String next = words[i + 1];

            List<String> bridgeWords = graph.getBridgeWords(current, next);
            if (bridgeWords != null && !bridgeWords.isEmpty()) {
                String bridge = bridgeWords.get(random.nextInt(bridgeWords.size()));
                result.add(bridge);
            }

            result.add(next);
        }

        String[] originalWords = inputText.split("\\s+");
        if (originalWords.length == result.size()) {
            for (int i = 0; i < originalWords.length; i++) {
                String original = originalWords[i];
                if (original.length() > 0 && Character.isUpperCase(original.charAt(0))) {
                    String word = result.get(i);
                    if (word.length() > 0) {
                        result.set(i, Character.toUpperCase(word.charAt(0)) + word.substring(1));
                    }
                }
            }
        }

        return String.join(" ", result);
    }

    public static void saveRandomWalk(List<String> walk, String fileName) {
        try (PrintWriter writer = new PrintWriter(fileName)) {
            writer.println(String.join(" ", walk));
            System.out.println("随机游走结果已保存到 " + fileName);
        } catch (FileNotFoundException e) {
            System.err.println("无法创建文件: " + e.getMessage());
        }
    }
}