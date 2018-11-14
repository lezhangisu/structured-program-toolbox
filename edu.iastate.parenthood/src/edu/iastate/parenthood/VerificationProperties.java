package edu.iastate.parenthood;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Properties;


public class VerificationProperties {
    
    private static String GRAPH_IMAGE_FILENAME_EXTENSION;

    private static Path OUTPUT_DIRECTORY;

    private static Path GOTO_GRAPHS_OUTPUT_DIRECTORY_PATH;
    
    
    static{
        Properties properties = new Properties();
        InputStream inputStream;
        try {
            inputStream = VerificationProperties.class.getClassLoader().getResourceAsStream("config.properties");
            properties.load(inputStream);
            
            OUTPUT_DIRECTORY = Paths.get(properties.getProperty("output_directory"));
            
            GRAPH_IMAGE_FILENAME_EXTENSION = properties.getProperty("graph_image_filename_extension");
            
            GOTO_GRAPHS_OUTPUT_DIRECTORY_PATH = Paths.get(OUTPUT_DIRECTORY.toFile().getAbsolutePath(), properties.getProperty("goto_graphs_output_directory_name"));
        
        } catch (IOException e) {
            System.err.println("Cannot locate the properties file.");
        }
    }
    
    
    public static Path getOutputDirectory(){
        return OUTPUT_DIRECTORY;
    }
    



    
    public static String getGraphImageFileNameExtension(){
        return GRAPH_IMAGE_FILENAME_EXTENSION;
    }

    
    public static Path getGraphsOutputDirectory(){
        return GOTO_GRAPHS_OUTPUT_DIRECTORY_PATH;
    }
    

}

